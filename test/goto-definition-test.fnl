(import-macros {: assert-matches : describe : it : before-each} :test.macros)
(local assert (require :luassert))

(local fennel (require :fennel))
(local {: ROOT-URI
        : setup-server} (require :test.util))

(local dispatch (require :fennel-ls.dispatch))
(local message  (require :fennel-ls.message))

(describe "jump to definition"

  (fn check [request-file line char response-file start-line start-col end-line end-col]
    (local state (doto [] setup-server))
    (let [message (dispatch.handle* state
                     (message.create-request 2 "textDocument/definition"
                       {:position {:character char :line line}
                        :textDocument {:uri (.. ROOT-URI "/" request-file)}}))
          uri (.. ROOT-URI "/" response-file)]
      (assert-matches
        message
        [{:jsonrpc "2.0" :id 2
          :result {: uri
                   :range {:start {:line start-line :character start-col}
                           :end   {:line end-line   :character end-col}}}}]
        (.. "expected position: " start-line " " start-col " " end-line " " end-col))))

  (it "handles (local _ (require XXX)"
    (check "example.fnl" 0 11 "foo.fnl" 0 0 0 0))

  (it "handles (require XXX))"
    (check "example.fnl" 1 5 "bar.fnl" 0 0 0 0))

  (it "can go to a fn"
    ;; TODO maybe it's better to just go to the name of the function, not the whole list
    (check "example.fnl" 9 3 "example.fnl" 4 0 7 20))

  (it "can go to a local"
    (check "example.fnl" 7 17 "example.fnl" 6 9 6 10))

  (it "can go to a function argument"
    (check "example.fnl" 5 9 "example.fnl" 4 9 4 10))

  (it "can handle variables shadowed with let"
    (check "example.fnl" 14 10 "example.fnl" 13 6 13 9))

  (it "can sort out the unification rule with match (variable unified)"
    (check "example.fnl" 19 12 "example.fnl" 17 8 17 9))

  (it "can sort out the unification rule with match (variable introduced)"
    (check "example.fnl" 20 12 "example.fnl" 20 9 20 10)))

  ;; (it "doesn't have ghost definitions from the same byte ranges as the macro files it's using")
  ;; (it "can go to a reference that occurs in a macro")
  ;; (it "can go to a function inside a table")
  ;; (it "can go to an field inside of a table")
  ;; (it "can go to a destructured local")
  ;; (it "can go to a destructured function argument")
  ;; (it "can go to a function in another file when accessed by multisym")
  ;; (it "can go to a function in another file imported via destructuring assignment")
  ;; (it "can work with a custom fennelpath")
  ;; (it "can go through more than one extra file")
  ;; (it "will give up instead of freezing on recursive requires")
  ;; (it "does slightly better in the presense of macros")
  ;; (it "finds the definition of macros")
  ;; (it "can follow import-macros")
  ;; (it "can go to the definition even in a lua file")
