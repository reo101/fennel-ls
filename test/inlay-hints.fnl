(local faith (require :faith))
(local {: ROOT-URI
        : ROOT-PATH
        : create-client} (require :test.utils.client))
(local {: get-markup} (require :test.utils))

(fn params-with-encodings [encodings]
  {:clientInfo {:name "my mock client" :version "9000"}
   :rootPath ROOT-PATH
   :rootUri ROOT-URI
   :workspaceFolders [{:name "foo" :uri ROOT-URI}]
   :capabilities {:general {:positionEncodings encodings}}
   :trace "off"})

(fn test-inlay-hints []
  ;; TODO: tests

  nil)

{: test-inlay-hints}
