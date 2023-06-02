"Language
The high level analysis system that does deep searches following
the data provided by compiler.fnl."

(local {: sym? : list? : sequence? : varg? : sym : view : list} (require :fennel))
(local utils (require :fennel-ls.utils))
(local state (require :fennel-ls.state))

(local get-ast-info utils.get-ast-info)

(local -require- (sym :require))
(local -dot- (sym :.))
(local -do- (sym :do))
(local -let- (sym :let))
(local -fn- (sym :fn))
(local -nil- (sym :nil))

(var search nil) ;; all of the search functions are mutually recursive

(λ stack-add-keys! [stack ?keys]
  "add the keys to the end of the stack in reverse order"
  (when ?keys
    (fcollect [i (length ?keys) 1 -1 &into stack]
      (. ?keys i)))
  stack)

(λ stack-add-split! [stack split]
  "add the split values to the end of the stack in reverse order"
  (fcollect [i (length split) 2 -1 &into stack]
    (. split i))
  stack)

(λ stack-add-multisym! [stack symbol]
  (stack-add-split! stack (utils.multi-sym-split symbol)))

(λ search-assignment [self file assignment stack opts]
  (let [{:binding _
         :definition ?definition
         :keys ?keys
         :fields ?fields} assignment]
    (if (and (= 0 (length stack)) opts.stop-early?)
        (values assignment file) ;; BASE CASE!!

        ;; search a virtual field from :fields
        (and (not= 0 (length stack)) (?. ?fields (. stack (length stack))))
        (search-assignment self file (. ?fields (table.remove stack)) stack opts)
        (search self file ?definition (stack-add-keys! stack ?keys) opts))))

(λ search-symbol [self file symbol stack opts]
  (if (= symbol -nil-)
    (values {:definition symbol} file) ;; BASE CASE !!
    (case (. file.references symbol)
      to (search-assignment self file to (stack-add-multisym! stack symbol) opts))))

(λ search-table [self file tbl stack opts]
  (if (. tbl (. stack (length stack)))
      (search self file (. tbl (table.remove stack)) stack opts)
      (= 0 (length stack))
      (values {:definition tbl} file) ;; BASE CASE !!
      nil)) ;; BASE CASE Give up

(λ search-list [self file call stack opts]
  (match call
    [-require- mod]
    (let [newfile (state.get-by-module self mod)]
      (when newfile
        (let [newitem (. newfile.ast (length newfile.ast))]
          (search self newfile newitem stack opts))))
    ;; A . form  indexes into item 1 with the other items
    [-dot- & split]
    (search self file (. split 1) (stack-add-split! stack split) opts)

    ;; A do block returns the last form
    [-do- & body]
    (search self file (. body (length body)) stack opts)

    [-let- _binding & body]
    (search self file (. body (length body)) stack opts)

    ;; functions evaluate to "themselves"
    [-fn-]
    (values {:definition call} file))) ;; BASE CASE !!

(set search
  (λ search [self file item stack opts]
    (if
        (sym? item)               (search-symbol self file item stack opts)
        (list? item)              (search-list self file item stack opts)
        (= :table (type item))    (search-table self file item stack opts)
        (= 0 (length stack))      {:definition item} ;; BASE CASE !!
        (error (.. "I don't know what to do with " (view item))))))

(λ search-main [self file symbol opts ?byte]
  "Find the definition of a symbol

It searches backward for the definition, and then the definition of that definition, recursively.
Over time, I will be adding more and more things that it can search through.

If a ?byte is provided, it will be used to determine what part of a multisym to search.

opts:
{:stop-early? boolean}

Imagine you have the following code:
```fnl
(local a 1)
(local b a)
b
```
If stop-early?, search-main will find the definition of `b` in (local b a).
Otherwise, it would continue and find the value 1.

Returns:
(values
  {:binding <where the symbol is bound. this would be the name of the function or variable>
   :definition <the best known definition>
   :keys <which part of the definition to look into. this can only possibly be present if stop-early?>
   :fields <other known fields which aren't part of the definition>}
  file)
"

  ;; The stack is the multi-sym parts still to search
  ;; for example, if I'm searching for "foo.bar.baz", my immediate priority is to find foo,
  ;; and the stack has ["baz" "bar"]. "bar" is at the "top"/"end" of the stack as the next key to search.
  (if (sym? symbol)
    (let [split (utils.multi-sym-split symbol (if ?byte (+ 1 (- ?byte symbol.bytestart))))
          stack (stack-add-split! [] split)]
      (local {:metadata METADATA
              :scopes {:global {:specials SPECIALS}}}
        (require :fennel.compiler))
      (case (. METADATA (. SPECIALS (tostring symbol)))
        metadata {: metadata}
        _ (case (. file.references symbol)
            ref (search-assignment self file ref stack opts)
            _ (case (. file.definitions symbol)
                def (search self file def.definition (stack-add-keys! stack def.keys) opts)))))))

(λ find-local-definition [file name ?scope]
  (when ?scope
    (or (. file.definitions-by-scope ?scope name)
        (find-local-definition file name ?scope.parent))))

(λ search-name-and-scope [self file name scope ?opts]
  (let [stack (stack-add-multisym! [] name)]
    (case (find-local-definition file name scope)
      def (search self file def.definition (stack-add-keys! stack def.keys) (or ?opts {})))))

(λ past? [?ast byte]
  ;; check if a byte is past an ast object
  (and (= (type ?ast) :table)
       (get-ast-info ?ast :bytestart)
       (< byte (get-ast-info ?ast :bytestart))
       false))

(λ contains? [?ast byte]
  ;; check if an ast contains a byte
  (and (= (type ?ast) :table)
       (get-ast-info ?ast :bytestart)
       (get-ast-info ?ast :byteend)
       (<= (get-ast-info ?ast :bytestart)
           byte
           (+ 1 (utils.get-ast-info ?ast :byteend)))))

(λ does-not-contain? [?ast byte]
  ;; check if a byte is in range of the ast
  (and (= (type ?ast) :table)
       (get-ast-info ?ast :bytestart)
       (get-ast-info ?ast :byteend)
       (not
         (<= (get-ast-info ?ast :bytestart)
             byte
             (+ 1 (get-ast-info ?ast :byteend))))))

(λ find-symbol [ast byte]
  (local parents [])
  (λ recurse [ast]
    (if
      (sym? ast)
      (values ast parents)
      (do
        (table.insert parents ast)
        (if
          (or (sequence? ast) (list? ast))
          (accumulate [(result done) nil
                       i child (ipairs ast)
                       &until result]
            (if (contains? child byte)
              (recurse child byte)))
          (and (not (sym? ast)) (not (varg? ast)))
          (accumulate [(result done) nil
                       key value (pairs ast)
                       &until done]
            (if (contains? key byte)
              (recurse key byte)
              (contains? value byte)
              (recurse value byte)))))))

  (values
    (accumulate [result nil i top-level-form (ipairs ast) &until result]
      (if (contains? top-level-form byte)
        (recurse top-level-form byte)))
    (fcollect [i 1 (length parents)]
      (. parents (- (length parents) i -1)))))


{: find-symbol
 : search-main
 : search-assignment
 : search-name-and-scope
 : search}
