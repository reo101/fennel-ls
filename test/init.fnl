((require :busted.runner))
(tset (require :fennel) :path "./?.fnl;./src/?.fnl")
(require :test.json-rpc-test)
(require :test.document-test)
(require :test.lsp-test)
