"Compiler
This file is responsible for the low level tasks of analysis. Its main job
is to recieve a file object and run all of the basic analysis that will be used
later by fennel-ls.language to answer requests from the client."

(local {: sym? : list? : sequence? : sym : view &as fennel} (require :fennel))
(local message (require :fennel-ls.message))
(local utils (require :fennel-ls.utils))

;; words surrounded by - are symbols,
;; because fennel doesn't allow 'require in a runtime file
(local -require- (sym :require))
(local -fn- (sym :fn))
(local -λ- (sym :λ))
(local -lambda- (sym :lambda))

(λ multisym? [t]
  ;; check if t is a symbol with multiple parts, eg. foo.bar.baz
  (and (sym? t)
    (let [t (tostring t)]
       (or (t:find "%.")
           (t:find ":")))))

(λ iter [t]
  ;; iterate through a list, sequence, or table
  (if (or (list? t)
          (sequence? t))
    (ipairs t)
    (pairs t)))

(local has-tables-mt
  {:__index
   (λ [self key]
     (let [val {}]
       (tset self key val)
       val))})

(λ compile [self file]
  "Compile the file, and record all the useful information from the compiler into the file object"
  ;; The useful information being recorded:
  (let [definitions-by-scope (doto {} (setmetatable has-tables-mt))
        definitions   {} ; symbol -> definition
        diagnostics   {} ; [diagnostic]
        references    {} ; symbol -> references
        scopes        {} ; ast -> scope
        require-calls {}]; ast -> boolean (does this ast start with the symbol `require)

    (λ find-definition [name ?scope]
      (when ?scope
        (or (. definitions-by-scope ?scope name)
            (find-definition name ?scope.parent))))

    (λ reference [ast scope]
      ;; Add a reference to the references
      (assert (sym? ast))
      ;; find reference
      (let [name (string.match (tostring ast) "[^%.:]+")
            target (find-definition (tostring name) scope)]
        (tset references ast target)))

    (λ define [?definition binding scope]
      ;; Add a definition to the definitions
      ;; recursively explore the binding (which, in the general case, is a destructuring assignment)
      ;; right now I'm not keeping track of *how* the symbol was destructured: just finding all the symbols for now.
      ;; also, there's no logic for (values)
      (λ recurse [binding keys]
        (if (sym? binding)
            (let [definition
                  {: binding
                   :definition ?definition
                   :keys (if (< 0 (length keys))
                           (fcollect [i 1 (length keys)]
                             (. keys i)))}]
              (tset (. definitions-by-scope scope) (tostring binding) definition)
              (tset definitions binding definition))
            (= :table (type binding))
            (each [k v (iter binding)]
              (table.insert keys k)
              (recurse v keys)
              (table.remove keys))))
      (recurse binding []))

    (λ define-function-name [ast scope]
      ;; add a function definition to the definitions
      (match ast
        (where [_fn name args]
          (and (sym? name)
               (sequence? args)))
        (let [def {:binding name :definition ast}]
          (if (multisym? name)
            (match (utils.multi-sym-split name)
              [ref field nil] ;; TODO more powerful function name metadata
              (let [target (find-definition ref scope)]
                (set target.fields (or target.fields {}))
                (tset target.fields field def)))

            (tset (. definitions-by-scope scope)
                  (tostring name)
                  def)))))

    (λ define-function-args [ast scope]
      ;; add the definitions of function arguments to the definitions
      (local args
        (match ast
          (where [_fn args] (fennel.sequence? args)) args
          (where [_fn _name args] (fennel.sequence? args)) args))
      (each [_ argument (ipairs args)]
        (define (sym :nil) argument scope))) ;; we say function arguments are set to nil

    (λ define-function [ast scope]
      ;; handle the definitions of a function
      (define-function-name ast scope))

    (λ compile-fn [ast scope]
      (tset scopes ast scope)
      (define-function-args ast scope))

    (λ compile-do [ast scope]
      (tset scopes ast scope))

    (λ call [ast scope]
      (tset scopes ast scope)
      ;; Most calls aren't interesting, but here's the list of the ones that are:
      (match ast
        ;; This cannot be done through the :fn feature of the compiler plugin system
        ;; because it needs to be called *before* the body of the function is processed.
        ;; TODO check if hashfn needs to be here
        [-fn-]
        (define-function ast scope)
        [-require- modname]
        (tset require-calls ast true)))

    (λ recoverable? [msg]
      (or (= 1 (msg:find "unknown identifier"))
          (= 1 (msg:find "expected closing delimiter"))
          (= 1 (msg:find "expected body expression"))
          (= 1 (msg:find "expected whitespace before opening delimiter"))
          (= 1 (msg:find "malformed multisym"))
          (= 1 (msg:find "expected at least one pattern/body pair"))))

    (λ on-compile-error [_ msg ast call-me-to-reset-the-compiler]
      (let [range (or (message.ast->range ast file)
                      (message.pos->range 0 0 0 0))]
        (table.insert diagnostics
          {:range range
           :message msg
           :severity message.severity.ERROR
           :code 201
           :codeDescription "compiler error"}))
      (if (recoverable? msg)
        true
        (do
          (call-me-to-reset-the-compiler)
          (error "__NOT_AN_ERROR"))))

    (λ on-parse-error [msg file line byte]
      ;; assume byte and char count is the same, ie no UTF-8
      (let [line (- line 1)
            range (message.pos->range line byte line byte)]
        (table.insert diagnostics
          {:range range
           :message msg
           :severity message.severity.ERROR
           :code 101
           :codeDescription "parse error"}))
      (if (recoverable? msg)
        true
        (error "__NOT_AN_ERROR")))

    (local allowed-globals (icollect [k v (pairs _G)] k))
    (table.insert allowed-globals :vim)

    ;; TODO clean up this code. It's awful now that there is error handling
    (let
      [macro-file? (= (: file.text :sub 1 24) ";; fennel-ls: macro-file")
       plugin
       {:name "fennel-ls"
        :versions ["1.3.1"]
        :symbol-to-expression reference
        : call
        :destructure define
        :assert-compile on-compile-error
        :parse-error on-parse-error
        :customhook-early-do compile-do
        :customhook-early-fn compile-fn}
       scope (fennel.scope)
       opts {:filename file.uri
             :plugins [plugin]
             :allowedGlobals allowed-globals
             :requireAsInclude false
             : scope}
       parser (partial pcall (fennel.parser file.text file.uri opts))
       ast (icollect [ok ok2 ast parser &until (not (and ok ok2))] ast)
       _compile-output (icollect [_i form (ipairs
                                            (if macro-file? [(fennel.list (sym :eval-compiler)
                                                                          ((or table.unpack _G.unpack) ast))]
                                              ast))]
                         (match (pcall fennel.compile form opts)
                           (where (nil err) (not= err "__NOT_AN_ERROR"))
                           (table.insert diagnostics
                             {:range (message.pos->range 0 0 0 0)
                              :message err})))]


      ;; write things back to the file object
      (set file.ast ast)
      (set file.scope scope)
      (set file.scopes scopes)
      (set file.definitions definitions)
      (set file.diagnostics diagnostics)
      (set file.references references)
      (set file.require-calls require-calls)
      (set file.allowed-globals allowed-globals))))
{: compile}
