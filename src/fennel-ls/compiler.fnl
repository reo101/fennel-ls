"Compiler
This module is responsible for calling the actual fennel parser and compiler,
and turning it into a \"fennel-ls file object\". It creates a plugin to the
fennel compiler, and then tries to store into it gets from the fennel
compiler's plugin hook callbacks. It stores lexical info about which
identifiers are declared / referenced in which places."

(local {: sym? : list? : sequence? : table? : sym : view &as fennel} (require :fennel))
(local message (require :fennel-ls.message))
(local utils (require :fennel-ls.utils))
(local searcher (require :fennel-ls.searcher))

(fn scope? [candidate]
  ;; just checking a couple of the fields
  (and
    (= (type candidate) :table)
    (= (type candidate.includes) :table)
    (= (type candidate.macros) :table)
    (= (type candidate.manglings) :table)
    (= (type candidate.specials) :table)
    (= (type candidate.gensyms) :table)))

;; words surrounded by - are symbols,
;; because fennel doesn't allow 'require in a runtime file
(local -require- (sym :require))
(local -include- (sym :include))
(local -fn- (sym :fn))
(local -lambda- (sym :lambda))
(local -λ- (sym :λ))

(λ ast->macro-ast [ast]
  [(fennel.list (sym :eval-compiler)
                ((or table.unpack _G.unpack) ast))])

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

(λ line+byte->range [self file line byte]
  (let [line (- line 1)
        ;; some errors in fennel erroneously say column -1
        ;; try compiling "(do\n" to see what I mean
        byte (math.max 0 byte)
        position (utils.pos->position file.text line byte self.position-encoding)]
    {:start position :end position}))


(λ compile [{:configuration {: macro-path} : root-uri &as self} file]
  "Compile the file, and record all the useful information from the compiler into the file object"
  ;; The useful information being recorded:
  (let [definitions-by-scope (doto {} (setmetatable has-tables-mt))
        definitions   {} ; symbol -> definition
        diagnostics   {} ; [diagnostic]
        references    {} ; symbol -> references
        scopes        {} ; ast -> scope
        calls         {} ; all calls in the macro-expanded code -> true
        lexical       {} ; all lists, tables, and symbols in the original source
        require-calls {}] ; the keys are all the calls that start with `require

    (λ find-definition [name ?scope]
      (if ?scope
        (or (. definitions-by-scope ?scope name)
            (find-definition name ?scope.parent))))

    (λ reference [symbol scope ref-type]
      (assert (or (= ref-type :read) (= ref-type :write) (= ref-type :mutate)) "wrong ref-type")
      (assert (sym? symbol) :not-a-symbol)
      (assert (scope? scope) :not-a-scope)
      ;; find reference
      (let [name (string.match (tostring symbol) "[^%.:]+")]
        (case (find-definition (tostring name) scope)
          target
          (if (. references symbol)
            (do ;; already exists
              (assert (= symbol (. references symbol :symbol)) (.. "the symbol should always be the same")))
              ;; (assert (= target (. references symbol :target)) (.. "different targets: " (view target) (view (. references symbol :target)))))
            (let [ref {: symbol : target : ref-type}]
              (tset references symbol ref)
              (table.insert target.referenced-by ref))))))

    (λ symbol-to-expression [ast scope ?reference?]
      (assert (sym? ast) "symbols only")
      (reference ast scope (if ?reference?
                             :read
                             (not (multisym? ast))
                             :write
                             :mutate)))

    (λ for-each-binding-in [binding ?definition action]
      (λ recurse [binding keys depth]
        (if (sym? binding)
            (action binding ?definition keys keys.multival)
            (list? binding)
            (let [nested? (not= depth 0)]
              (if nested? (error (.. "I didn't expect to find a nested multival destructure in " (view binding) " at " (view keys))))
              (each [i child (ipairs binding)]
                (set keys.multival i)
                (recurse child keys (+ depth 1))
                (set keys.multival nil)))
            (table? binding)
            (accumulate [prev nil
                         key child (iter binding)]
              (if (or (sym? key :&as) (sym? prev :&as))
                  ;; if its &as, just keep the keys the same
                  (recurse child keys (+ depth 1))
                  (or (sym? key :&) (sym? prev :&))
                  ;; currently the "rest" param is defined to []
                  (for-each-binding-in child [] action)
                  (or (sym? child :&as) (sym? child :&))
                  child
                  (do
                    (table.insert keys key)
                    (recurse child keys (+ depth 1))
                    (table.remove keys))))))
      (recurse binding [] 0))

    (λ define [?definition binding scope ?opts]
      (for-each-binding-in binding ?definition
        (fn [symbol ?definition keys ?multival]
          (let [definition
                {:binding symbol
                 :definition ?definition
                 :referenced-by (or (?. definitions symbol :referenced-by) [])
                 :keys (if (. keys 1)
                         (icollect [_ v (ipairs keys)] v))
                 :multival ?multival
                 :var? (?. ?opts :isvar)
                 : file}]
            (tset (. definitions-by-scope scope) (tostring symbol) definition)
            (tset definitions symbol definition)))))

    (λ mutate [_?definition binding scope]
      (for-each-binding-in binding _?definition
        (fn [symbol _?definition _keys]
          (when (not (multisym? symbol))
            (reference symbol scope :write)
            (if (. references symbol)
              (tset (. references symbol :target) :var-set true))))))

    (λ destructure [to from scope {:declaration ?declaration? : symtype &as opts}]
      ;; I really don't understand symtype
      ;; I think I need an explanation
      (if ?declaration?
        (define to from scope opts)
        (mutate to from scope)))

    (λ add-field [ast multisym scope]
      "the multisym has the main name and the root name"
      (case-try (utils.multi-sym-split multisym)
        [ref field nil] ;; TODO more powerful function name metadata
        (find-definition ref scope)
        target
        (do
          (set target.fields (or target.fields {}))
          (tset target.fields field
            {:binding multisym
             :definition ast
             :file file}))))
             ;; ;; referenced-by inherits from all other symbols
             ;; :referenced-by (or (?. definitions multisym :referenced-by) [])}))))

    (λ define-function-name [ast scope]
      ;; add a function definition to the definitions
      (case ast
        (where [_fn name args]
          (and (sym? name)
               (sequence? args)))
        (if (multisym? name)
          (add-field ast name scope)
          (define ast name scope))))

    (λ define-function-args [ast scope]
      ;; add the definitions of function arguments to the definitions
      (local args
        (case ast
          (where [_fn args] (fennel.sequence? args)) args
          (where [_fn _name args] (fennel.sequence? args)) args
          _ []))
      (each [_ argument (ipairs args)]
        (if (not (sym? argument :&))
          (define (sym :nil) argument scope)))) ;; TODO  for now, function arguments are set to nil

    (λ define-function [ast scope]
      ;; handle the definitions of a function
      (define-function-name ast scope))

    (λ compile-for [ast scope binding]
       (define (sym :nil) binding scope))

    (λ compile-each [ast scope bindings]
      (each [_ binding (ipairs bindings)]
        (define (sym :nil) binding scope)))

    (λ compile-fn [ast scope]
      (tset scopes ast scope)
      (define-function-args ast scope))

    (λ compile-do [ast scope]
      (tset scopes ast scope))

    (λ call [ast scope]
      (tset calls ast true)
      (tset scopes ast scope)
      ;; Most calls aren't interesting, but here's the list of the ones that are:
      (case ast
        ;; This cannot be done through the :fn feature of the compiler plugin system
        ;; because it needs to be called *before* the body of the function is processed.
        ;; TODO check if hashfn needs to be here
        (where (or [(= -fn-)] [(= -lambda-)] [(= -λ-)]))
        (define-function ast scope)
        (where (or [(= -require-) _modname]
                   [(= -include-) _modname]))
        (tset require-calls ast true)
        ;; fennel expands multisym calls into the `:` special, so we need to reference the symbol while we still can
        (where [sym] (multisym? sym) (: (tostring sym) :find ":"))
        (reference sym scope :read)))

    (local defer [])

    (λ attempt-to-recover! [msg ?ast]
      (or (= 1 (msg:find "unknown identifier"))
          (= 1 (msg:find "local %S+ was overshadowed by a special form or macro"))
          (= 1 (msg:find "expected var "))
          (= 1 (msg:find "cannot call literal value"))
          (= 1 (msg:find "unexpected vararg"))
          (= 1 (msg:find "expected closing delimiter"))
          (= 1 (msg:find "expected body expression"))
          (= 1 (msg:find ".*fennel/macros.fnl:%d+: expected body"))
          (= 1 (msg:find "expected condition and body"))
          (= 1 (msg:find "expected whitespace before opening delimiter"))
          (= 1 (msg:find "malformed multisym"))
          (= 1 (msg:find "expected at least one pattern/body pair"))
          (= 1 (msg:find "module not found"))
          (= 1 (msg:find "expected even number of values in table literal"))
          (= 1 (msg:find "use $%.%.%. in hashfn"))
          (when (and (= 1 (msg:find "expected even number of name/value bindings"))
                     (sequence? ?ast)
                     (= 1 (% (length ?ast) 2)))
            (table.insert ?ast (sym :nil))
            (table.insert defer #(table.remove ?ast))
            true)
          (when (and (= 1 (msg:find "expected a function, macro, or special to call"))
                     (list? ?ast)
                     (= (length ?ast) 0))
            (table.insert ?ast (sym :do))
            (table.insert defer #(table.remove ?ast))
            true)
          (when (= 1 (msg:find "unexpected multi symbol"))
            (let [old (tostring ?ast)]
              (tset ?ast 1 "!!invalid-multi-symbol!!")
              (table.insert defer #(tset ?ast 1 old))
              true))))


    (λ on-compile-error [_ msg ast call-me-to-reset-the-compiler]
      (let [range (or (message.ast->range self file ast)
                      (line+byte->range self file 1 1))]
        (table.insert diagnostics
          {:range range
           :message msg
           :severity message.severity.ERROR
           :code 201
           :codeDescription "compiler error"}))
      (if (attempt-to-recover! msg ast)
        true
        (do
          (call-me-to-reset-the-compiler)
          (error "__NOT_AN_ERROR"))))

    (λ on-parse-error [msg filename line byte _source call-me-to-reset-the-compiler]
      (let [line (if (= line "?") 1 line)
            range (line+byte->range self file line byte)]
        (table.insert diagnostics
          {:range range
           :message msg
           :severity message.severity.ERROR
           :code 101
           :codeDescription "parse error"}))
      (if (attempt-to-recover! msg)
        true
        (do
          (call-me-to-reset-the-compiler)
          (error "__NOT_AN_ERROR"))))

    (local allowed-globals
      (icollect [k _ (pairs _G)]
        k))
    (each [_ v (ipairs (utils.split-spaces self.configuration.extra-globals))]
      (table.insert allowed-globals v))

    ;; TODO clean up this code. It's awful now that there is error handling
    (let [macro-file? (= (file.text:sub 1 24) ";; fennel-ls: macro-file")
          plugin
          {:name "fennel-ls"
           :versions ["1.4.1" "1.4.2" "1.5.0" "1.5.1" "1.5.2"]
           : symbol-to-expression
           : call
           : destructure
           ;; : macroexpand
           ;; :fn    fn-hook
           ;; :do    there's a do hook
           ;; :chunk I don't know what this one is
           :assert-compile on-compile-error
           :parse-error on-parse-error
           :pre-for compile-for
           :pre-each compile-each
           :pre-fn compile-fn
           :pre-do compile-do}
          scope (fennel.scope)
          opts {:filename file.uri
                :plugins [plugin]
                :allowedGlobals allowed-globals
                :requireAsInclude false
                : scope}
          filter-errors (fn _filter-errors [component ...]
                          (case ...
                            (true ?item1 ?item2) (values ?item1 ?item2)
                            (where (or (nil err) (false err)) (not (err:find "^[^\n]-__NOT_AN_ERROR\n")))
                            (if (os.getenv :TESTING)
                              (error (.. "\nYou have crashed fennel-ls (or the fennel " component ") with the following message\n:" err
                                         "\n\n^^^ the error message above here is the root problem\n\n"))
                              (table.insert diagnostics
                                {:range (line+byte->range self file 1 1)
                                 :message (.. "unrecoverable " component " error: " err)}))))

          parser (let [p (fennel.parser file.text file.uri opts)]
                   (fn _p1 [p2 p3]
                     (filter-errors :parser (xpcall #(p p2 p3) fennel.traceback))))

          ast (icollect [ok ast parser &until (not ok)] ast)]

      (λ collect-everything [ast result]
        (when (or (table? ast) (list? ast) (sym? ast))
          (tset result ast true))
        (when (or (table? ast) (list? ast))
          (each [k v (iter ast)]
            (collect-everything k result)
            (collect-everything v result))))

      (collect-everything ast lexical)



      ;; This is bad; we mutate fennel.macro-path
      (let [old-macro-path fennel.macro-path]
        (set fennel.macro-path
             (searcher.add-workspaces-to-path macro-path [root-uri]))

        ;; compile
        (each [_i form (ipairs (if macro-file? (ast->macro-ast ast) ast))]
          (filter-errors :compiler (xpcall #(fennel.compile form opts) fennel.traceback)))

        (set fennel.macro-path old-macro-path))

      (each [_ cmd (ipairs defer)]
        (cmd))

      (set file.ast ast)
      (set file.calls calls)
      (set file.lexical lexical)
      (set file.scope scope)
      (set file.scopes scopes)
      (set file.definitions definitions)
      (set file.definitions-by-scope definitions-by-scope)
      (set file.diagnostics diagnostics)
      (set file.references references)
      (set file.require-calls require-calls)
      (set file.allowed-globals allowed-globals))))

{: compile}
