(local faith (require :faith))
(local {: create-client-with-files
        : position-past-end-of-text} (require :test.utils))
(local {: view} (require :fennel))

(local kinds
  {:Text 1 :Method 2 :Function 3 :Constructor 4 :Field 5 :Variable 6 :Class 7
   :Interface 8 :Module 9 :Property 10 :Unit 11 :Value 12 :Enum 13 :Keyword 14
   :Snippet 15 :Color 16 :File 17 :Reference 18 :Folder 19 :EnumMember 20
   :Constant 21 :Struct 22 :Event 23 :Operator 24 :TypeParameter 25})

(fn find [completions e]
  (accumulate [result nil
               i c (ipairs completions)
               &until result]
    (if (or (and (= (type e) :string)
                 (= c.label e))
          (and (= (type e) :table)
               (or (= e.label nil)
                   (and (= (type e.label) :string) (= e.label c.label))
                   (and (= (type e.label) :function) (e.label c.label)))
               (or (= e.kind nil)
                   (and (= (type e.kind) :number) (= e.kind c.kind))
                   (and (= (type e.kind) :function) (e.kind c.kind)))
               (or (= e.documentation nil)
                   (and (= (type e.documentation) :string) (= e.documentation c.documentation))
                   (and (= (type e.documentation) :function) (e.documentation c.documentation))
                   (and (= e.documentation true) (not= nil c.documentation)))
               (or (= e.textEdit nil)
                   (and (= e.textEdit.range.start.line      c.textEdit.range.start.line)
                        (= e.textEdit.range.start.character c.textEdit.range.start.character)
                        (= e.textEdit.range.end.line        c.textEdit.range.end.line)
                        (= e.textEdit.range.end.character   c.textEdit.range.end.character)))))
      i)))

(fn check [file-contents expected unexpected]
  (let [{: self : uri : cursor : text} (create-client-with-files file-contents)
        [{:result ?result}] (self:completion uri
                              (or cursor
                                  (position-past-end-of-text text)))
        completions (or ?result [])]

    (each [_ e (ipairs unexpected)]
      (let [i (find completions e)]
        (faith.= nil i (.. "Got unexpected completion: " (view e) "\n"
                           "from:    " (view file-contents) "\n"
                           (view (. completions i) {:escape-newlines? true})))))

    (each [_ e (ipairs expected)]
      (let [i (find completions e)]
        (faith.is i (.. "Didn't get completion: " (view e) "\n"
                        "from:    " (view file-contents) "\n"
                        (if (= (type e) :table)
                          (let [candidate (find completions {:label e.label})]
                            (if candidate
                              (.. "Candidate that didn't match:\n"
                                  (view (. completions candidate)
                                        {:escape-newlines? true}))
                              ""))
                          "")))))))

(fn test-global []
  ;; TODO shouldn't this kind be Function?
  (check "(" [{:label :setmetatable :kind kinds.Variable}] [])
  (check "(" [:_G :debug :table :io :getmetatable :setmetatable :_VERSION :ipairs :pairs :next] [:this-is-not-a-global])
  (check "#nil\n(" [:_G :debug :table :io :getmetatable :setmetatable :_VERSION :ipairs :pairs :next] [])
  (check "(if ge" [:getmetatable] [])
  nil)

(fn test-local []
  (check "(local x 10)\n(print |)" [:x] [:+])
  (check "(local x (doto 10 or and +))\n(print |)" [:x] [])
  (check "(local x 10)\n|\n" [:x] [])
  (check "(do (local x 10))\n|" [] [:x])
  (check "(let [foo 10 bar 20]
            |)" [:foo :bar] [])
  (check "(let [foo 10]
            (let [bar 20]
              |))" [:foo :bar] [])
  (check "(let [foo 10]
            (let [bar 20]
              fo|))" [:foo :bar] [])
  (check "(let [foo 10]
            (let [bar 20]
              |" [:foo :bar] [])
  (check "(let [foo 10]
            (let [bar 20]
              fo|" [:foo :bar] [])
  (check "(local foo 10)
          (local bar (let [y foo] |" [:foo :y] [])
  (check "(let [foo 10
                bar 20
                _ |" [:foo :bar] [])
  (check "(let [foo 10
                bar 20
                _ fo|" [:foo :bar] [])
  (check "(local x {:field 100})\n(if x.fi" [:field] [])
  nil)

(fn test-builtin []
  (check "(|)" [:do :let :fn :doto :-> :-?>> :?.] [])
  ;; it's not the language server's job to do filtering,
  ;; so there's no negative assertions here for other symbols
  (check "(d|)" [:do :doto] [])
  ;; in fact, for fuzzy-matching clients, you especially want to make sure the server isn't filtering
  (check "(t|)" [:doto :setmetatable] [])
  ;; specials only are suggested in callable positions
  (check "(do |)" [] [:do :let :fn :-> :-?>> :?.])
  (check "|\n" [] [:do :let :fn :-> :-?>> :?.])
  (check "d|\n" [] [:do :let :fn :-> :-?>> :?.])
  nil)

(fn test-macro []
  (check "(macro funny [] `nil)\n(|)" [:funny] [])
  nil)

(fn test-local-in-macro []
  (check "(local item 10)\n(doto it|)" [:item] [])
  (check "(local item 10)\n(doto |)" [:item] [])
  (check "(local item 10)\n(case 1 1 it|)" [:item] [])
  (check "(local item 10)\n(case 1 1 |)" [:item] [])
  nil)

(fn test-fn-arg []
  (check "(fn [x] (print x))\n" [] [:x])
  (check "(fn [x] (print x))\n(print " [] [:x])
  (check "(fn foo [z]\n  (let [x 10 y 20]\n    |" [:x :y :z] [])
  (check "(fn foo [arg1 arg2 arg3]\n  |)" [:arg1 :arg2 :arg3] [])
  (check "(fn foo [arg1 arg2 arg3]\n  (do (do (do |))))" [:arg1 :arg2 :arg3] [])
  nil)

(fn test-field []
  (check "(local x {:field (fn [])})\n(x:" [:field] [:local])
  ;; regression test for not crashing
  (check "(local x {:field (fn [])})\n(x::f" [] [])
  (check
    "(let [my-table {:foo 10 :bar 20}]\n  my-table.|)))"
    [:foo :bar]
    [:_G :local :doto :+]) ;; no globals, specials, macros, or others
  (check
    {:main.fnl "(let [foo (require :fooo)]
                    foo.|)))"
     :fooo.fnl "(fn my-export [x] (print x))
                {: my-export :constant 10}"}
    [:my-export :constant]
    [:_G :local :doto :+])
  (check
    {:main.fnl "(let [foo (require :fooo)]
                    foo.|)))"
     :fooo.fnl "(local M {:constant 10})
                (fn M.my-export [x] (print x))
                M"}
    [:my-export :constant]
    [:_G :local :doto :+]) ;; no globals, specials, macros, or others
  (check "(local x {:field (fn [])})\n(x:fi|" [:field] [:table])
  nil)

(fn test-docs []
  (check "(fn xyzzy [x y z] \"docstring\" nil)\n(xyzz"
    [{:label :xyzzy :kind kinds.Variable :documentation true}] ;; TODO shouldn't this be kinds.Function
    [])

  (local things-that-are-allowed-to-have-missing-docs
    {:lua 1 :set-forcibly! 1 :unpack 1 :setfenv 1 :getfenv 1 :module 1 :newproxy 1 :gcinfo 1 :loadstring 1 :bit 1 :jit 1 :bit32 1})

  (check "("
    [;; builtin specials
     {:label :local
      :kind kinds.Operator
      :documentation true
      :textEdit {:range {:start {:line 0 :character 1}
                         :end   {:line 0 :character 1}}}}
     ;; builtin macros
     {:label :-?>
      :kind kinds.Keyword
      :documentation true}]
    [{:documentation #(= nil $) :label #(not (. things-that-are-allowed-to-have-missing-docs $))}
     {:kind #(= nil $)          :label #(not (. things-that-are-allowed-to-have-missing-docs $))}
     {:label #(= nil $)}])

  (check "(let [x (fn x [a b c]
                    \"\"\"docstring\"\"\"
                     nil)
                t {: x}]
            (t."
    [:x]
    [:_G
     {:documentation #(= nil $)}
     {:kind #(= nil $)}
     {:label #(= nil $)}])

  nil)

(fn test-module []
  (check "(coroutine.y|"
    [{:label "yield"
      :documentation #(and $.value ($.value:find "```fnl\n(yield ...)\n```" 1 true))}]
    ["coroutine" "_G" "do"
     {:documentation #(= nil $)}])
  (check "(local c coroutine)
          (c.y"
    [{:label "yield"}]
    ["coroutine" "_G" "do"])
  (check "(local t table)
          (t.i"
    ["insert"]
    [{:documentation #(= nil $)}])
  nil)
;; ;; Future tests / features
;; ;; Scope Ordering Rules
;; (it "does not suggest locals past the suggestion location when a symbol is partially typed")
;; (it "does not suggest locals past the suggestion location without a symbol")
;; (it "does not suggest locals past the suggestion point at the top level")
;; (it "does not suggest items from later definitions in the same `let`")
;; (it "does suggest items from earlier definitions in the same `let`")
;; (it "does not suggest macros defined from later definitions")

;; (it "suggests fields of strings"))
  ;; (it "offers rich information about variable completions")
  ;; (it "offers rich information about field completions")
  ;; (it "offers rich information about method completions")
  ;; (it "offers rich information about module completions")
  ;; (it "offers rich information about macro-module completions")))
;; (it "suggests known fn keys when using the `:` special")
;; (it "suggests known keys when using the `.` special")
;; (it "suggests known module names in `require` and `include` and `import-macros` and `require-macros` and friends")
;; (it "knows the fields of the standard lua library.")
;; (it "does not suggest special forms for the \"call\" position when a list isn't actually a call, ie destructuring assignment")
;; (it "suggests keys when typing out destructuring, as in `(local {: typinghere} (require :mod))`")
;; (it "only suggests tables for `ipairs` / begin work on type checking system")

{: test-global
 : test-local
 : test-builtin
 : test-macro
 : test-local-in-macro
 : test-fn-arg
 : test-field
 : test-docs
 : test-module}
