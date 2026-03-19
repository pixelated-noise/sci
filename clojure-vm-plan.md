# Clojure Explicit Stack VM — Implementation Plan

> Fork of SCI. `src/` deleted. Goal: implement a serialisable, freeze/resume-capable
> Clojure interpreter using an explicit stack VM, validated against SCI's test suite.

---

## Phase 0: Project Scaffold

**Goal:** Get the repo building and tests runnable with zero passes (but no compilation errors).

- Keep SCI's `test/`, `deps.edn`, `project.clj` as-is
- Delete `src/`
- Create `src/sci/` and stub out the minimum public API surface SCI's tests expect: `sci.core` with `eval-string`, `eval-form`, `init`, `eval-string*`
- Create a test runner script that reports pass/fail counts — this becomes your progress dashboard
- Make all tests fail with `"not implemented"` rather than compile errors

**Deliverable:** `clj -M:test` runs and reports `0 passed, N failed`.

---

## Phase 1: Core Data Structures

**Goal:** Define the machine. Everything else builds on this.

```clojure
;; The entire interpreter state — always a plain serialisable map
{:stack  []        ; vector of frames, top = last
 :env    {}        ; current lexical env: symbol -> value
 :ns     {}        ; namespace table: sym -> {vars, aliases, imports}
 :heap   {}        ; interned vars: qualified-sym -> {:val :meta :dynamic?}
 :result nil       ; holds the most recently computed value
 :status :running  ; :running | :done | :suspend | :effect
 :effect nil}      ; when :effect, describes the requested side effect
```

Frame types to define up front (each is a plain map with an `:op` key):

```
:eval          {:op :eval,        :expr <form>}
:apply         {:op :apply,       :f <val>,  :args <vals>}
:eval-args     {:op :eval-args,   :f <val>, :pending [forms...], :done [vals...]}
:if            {:op :if,          :then <form>, :else <form>}
:do            {:op :do,          :remaining [forms...]}
:let           {:op :let,         :bindings [...], :body [...], :env <env>}
:def           {:op :def,         :name <sym>, :ns <sym>}
:fn-body       {:op :fn-body,     :params [...], :body [...], :env <env>}
:loop          {:op :loop,        :bindings [...], :body [...], :env <env>}
:recur-target  {:op :recur-target}   ; marker so recur knows where to jump
:try           {:op :try,         :catches [...], :finally <form>}
:throw         {:op :throw}
:set!          {:op :set!,        :target <sym>}
:effect-resume {:op :effect-resume}  ; re-entry point after an effect resolves
```

Write `push-frame`, `pop-frame`, `push-value` (pops top frame, pushes `:result`) helpers.

**No tests pass yet, but the data model is locked.**

---

## Phase 2: Reader

**Goal:** Turn strings into forms.

Don't write a reader from scratch — pull in `org.clojure/tools.reader` as a dependency.
Wire it into your `eval-string` entry point. SCI's `read_test.cljc` and `parse_test.cljc`
will validate edge cases.

```clojure
(defn read-all [s]
  (tools.reader/read-all (tools.reader.string-reader/make-reader s)))
```

The reader produces standard Clojure data (symbols, lists, maps, vectors) — exactly what
your VM consumes.

**Target:** `read_test.cljc` passes.

---

## Phase 3: The Step Function & Minimal Eval

**Goal:** Literals, symbols, `if`, `do`, basic `fn`, `let`, function application —
enough for the first chunk of `core_test.cljc`.

The entire interpreter is one `step` function:

```clojure
(defn step [machine]
  (let [frame (peek (:stack machine))]
    (case (:op frame)
      :eval      (step-eval machine frame)
      :apply     (step-apply machine frame)
      :eval-args (step-eval-args machine frame)
      :if        (step-if machine frame)
      :do        (step-do machine frame)
      :let       (step-let machine frame)
      :def       (step-def machine frame)
      :fn-body   (step-fn-body machine frame)
      nil        (assoc machine :status :done))))  ; empty stack = done
```

And a run loop:

```clojure
(defn run [machine]
  (loop [m machine]
    (case (:status m)
      :running  (recur (step m))
      :done     (:result m)
      :suspend  m          ; caller gets the frozen machine back
      :effect   m)))       ; caller handles the effect, then calls run again
```

Implement in this order, validating against tests after each:

1. **Literals** — numbers, strings, keywords, nil, booleans, vectors, maps, sets → just push the value
2. **Symbols** — look up in `:env`, then `:heap`
3. **`if`** — eval condition, push `:if` frame with then/else
4. **`do`** — push remaining forms, eval one at a time
5. **`fn*`** — create a `{:type :closure, :params [...], :body [...], :env <current-env>}` value
6. **Application** — if fn is a closure, push `:fn-body` frame with extended env; if host fn, call directly
7. **`let*`** — eval bindings sequentially, extending env

**Target:** First ~100 assertions in `core_test.cljc` pass.

---

## Phase 4: Definitions, Namespaces, Vars

**Goal:** `def`, `defn`, `ns`, `require`, dynamic vars, `binding`.

- `def` writes into `:heap` at the qualified key `current-ns/name`
- `defn` is just `def` + `fn*` (implement as a special form initially, replace with real macro later)
- Namespaces: `:ns` table holds `{:vars #{} :aliases {} :refers {}}`
- Dynamic vars: `{:dynamic? true :val <thread-local-stack>}` in heap — push/pop a binding stack in the machine state
- `var` / `#'` — return the var map itself

**Target:** `namespaces_test.cljc`, `vars_test.cljc`, `repl_test.cljc` largely pass.

---

## Phase 5: Loop/Recur & TCO

**Goal:** `loop`, `recur`, recursive `defn`.

Since you control the stack, recur is just:

```clojure
:recur
;; pop frames until we find :recur-target (loop or fn-body marked as recur target)
;; rebind the target's params to the recur args
;; re-push the body
```

Key rules:
- Every `fn-body` and `loop` frame gets marked as a recur target
- `recur` at non-tail position is a compile-time error (validate during the `:eval` step
  for recur forms before pushing frames)
- `trampoline` works for free since you're already on a real loop

**Target:** `recur-test`, `loop-test` pass. Infinite recursion via `recur` doesn't stack overflow.

---

## Phase 6: Macros & Special Forms

**Goal:** Full macro system, all remaining special forms.

Special forms to implement:

- `quote`, `syntax-quote` (unquote, unquote-splicing need special handling during expansion)
- `defmacro` — stores closure with `{:macro? true}` flag; applied at `:eval` time, not `:apply` time
- `macroexpand`, `macroexpand-1`
- `case` — compile to decision tree during eval
- `try/catch/finally` — push `:try` frame; on throw, unwind stack looking for matching catch
- `throw`
- `letfn`
- `set!` for dynamic vars
- `new`, `.method`, `.-field` (Java interop — push to host fast path)

For `try/catch`: when an exception/throw occurs, walk back the `:stack` looking for a `:try`
frame with a matching catch clause. The explicit stack makes this clean.

**Target:** `error_test.cljc`, macro portions of `core_test.cljc` pass.

---

## Phase 7: Host Interop Fast Path

**Goal:** Calling Clojure/Java functions efficiently without VM overhead.

Mark every host function as a host callable:

```clojure
{:type :host-fn, :fn clojure.core/map}
```

In `:apply`:

```clojure
(if (= :host-fn (:type f))
  ;; bypass stack entirely
  (-> machine pop-frame (push-value (apply (:fn f) args)))
  ;; push interpreted fn body
  ...)
```

Pre-populate `:heap` with all of `clojure.core` wrapped as `:host-fn`. This gives you the
full standard library essentially for free, and makes it fast.

**Target:** `interop_test.cljc` passes. Performance noticeably better.

---

## Phase 8: Protocols, Multimethods, Records

**Goal:** `defprotocol`, `extend-type`, `defmulti`, `defmethod`, `defrecord`, `deftype`, `reify`.

- **Multimethods:** store in heap as `{:type :multimethod, :dispatch-fn f, :methods {dispatch-val -> fn}}`
- **Protocols:** store as `{:type :protocol, :methods #{...}}`; `extend-type` registers
  implementations in a global `{:protocol-impls {type -> {method -> fn}}}` table in machine state
- **Records:** `defrecord` generates a map-like type with a tag; implement as
  `{:type :record, :record-type RecName, :fields {...}}`
- **`reify`:** similar to record but anonymous

**Target:** `protocols_test.cljc`, `multimethods_test.cljc`, `defrecords_and_deftype_test.cljc`,
`reify_test.cljc` pass.

---

## Phase 9: Freeze / Resume

**Goal:** Snapshot the machine at any `step` boundary and resume it later.

### Serialisable host fn references

Don't store host fns directly in the heap — store a keyword reference instead:

```clojure
;; In heap, store a reference, not the fn itself:
{:type :host-fn-ref, :id :clojure.core/map}

;; At startup, register the lookup table once:
(def host-fn-registry
  {:clojure.core/map  map
   :clojure.core/inc  inc
   ...})
```

When you thaw a machine, re-hydrate `:host-fn-ref` → `:host-fn` by looking up the registry.
The frozen bytes contain no JVM objects.

### Freeze / thaw

```clojure
(defn freeze! [machine]
  (nippy/freeze machine))

(defn thaw! [bytes]
  (nippy/thaw bytes))
```

### Suspension points

The interpreted code can call `suspend!` to yield voluntarily:

```clojure
;; Interpreted code:
(suspend! {:reason :waiting-for-approval, :data {:amount 1000}})

;; VM: sets :status :suspend, returns machine to caller
```

Or model it as an **effect** — the interpreted code declares what it needs, the host does it:

```clojure
;; Interpreted code:
(effect! {:type :http/get, :url "https://..."})

;; VM: pushes :effect-resume frame, sets :status :effect, returns machine to caller
;; Caller performs the HTTP call, injects result, calls (run machine) again
```

### Additional machine keys for freeze/resume

```clojure
{...
 :suspend-data nil   ; arbitrary data passed to suspend!
 :effect       nil   ; {:type :http/get, :url "..."} etc.
 :effect-k     nil}  ; the continuation frame to resume into
```

### Full lifecycle

```clojure
;; Start
(def m (machine/init {:source "(my-workflow)"}))
(def m (run m))

;; m is :suspend or :effect — freeze it
(def checkpoint (freeze! m))
(store-somewhere! checkpoint)

;; Later, on a different JVM:
(def m (thaw! (fetch-checkpoint!)))
(def m (if (= :effect (:status m))
         (-> m
             (inject-effect-result {:body "...response..."})
             run)
         (run m)))
```

**Deliverable:** `freeze-resume-test.cljc` — write this file first as the spec,
then implement until it passes.

---

## Phase 10: Permissions & Security

SCI has a rich allow/deny system. Implement as a validation step during `:eval`:

```clojure
(defn check-permission! [machine sym]
  (let [{:keys [allow deny]} (:permissions machine)]
    (when (and allow (not (contains? allow sym)))
      (throw (ex-info (str sym " not allowed") {})))
    (when (contains? deny sym)
      (throw (ex-info (str sym " not allowed") {})))))
```

**Target:** `permission-test` section of `core_test.cljc` passes.

---

## Phase 11: Polish & Remaining Tests

Work through remaining test files in order of complexity:

1. `hierarchies_test.cljc` — `derive`, `isa?`, `ancestors`
2. `core_protocols_test.cljc` — `ISeq`, `ILookup` etc. on your record types
3. `error_test.cljc` — precise error messages and location metadata
4. `copy_ns_test_ns.cljc` — namespace copying API
5. `pprint_test.clj` — delegate to host `clojure.pprint`
6. `proxy_test.clj`, `array_test.clj` — JVM-only, tackle last

---

## Suggested File Structure

```
src/
  gvm/              ; your project name — not "sci" to avoid confusion
    core.clj        ; public API matching sci.core surface
    reader.clj      ; wraps tools.reader
    machine.clj     ; machine map constructors, push/pop helpers
    step.clj        ; the step function + all step-* handlers
    env.clj         ; lexical env operations
    ns.clj          ; namespace table operations
    heap.clj        ; var storage, dynamic binding stacks
    host.clj        ; host-fn-registry, host-fn-ref resolution
    freeze.clj      ; freeze!/thaw!, serialisability validation
    interop.clj     ; Java interop handlers
    protocols.clj   ; protocol/multimethod dispatch tables
    error.clj       ; error construction with location metadata
```

The test shim in `test/sci/test_utils.cljc` is what most tests go through — repoint that
to `gvm.core` and the majority of tests work unchanged.

---

## Claude Code Tips

- **One phase at a time.** Give it a phase, ask it to make tests pass, review, commit.
- **Red/green anchors.** Always start with `clj -M:test 2>&1 | grep -E "PASS|FAIL|ERROR" | wc -l`
  so you have a number to beat.
- **Lock the data structures early.** The machine map schema should be treated as frozen —
  changes require explicit approval. Frame type proliferation is the main source of chaos.
- **Keep `step` flat.** Each `step-*` handler should be ~10–20 lines. If a handler grows
  large, it's doing too much.
- **Freeze tests as a first-class citizen.** Write `freeze-resume-test.cljc` in Phase 9
  before implementing — use it as the spec, not an afterthought.
- **Host fn registry completeness.** In Phase 7, generate the registry programmatically
  from `clojure.core`'s public vars rather than listing them by hand.
