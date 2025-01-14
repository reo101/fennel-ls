(local faith (require :faith))
(local {: create-client-with-files} (require :test.utils))
(local {: null} (require :fennel-ls.json.json))
(local {: view} (require :fennel))

(fn location-comparator [a b]
 (or (< a.uri b.uri)
     (and (= a.uri b.uri)
          (or (< a.range.start.line b.range.start.line)
              (and (= a.range.start.line b.range.start.line)
                   (or (< a.range.start.character b.range.start.character)
                       (and (= a.range.start.character b.range.start.character)
                           (or (< a.range.end.line b.range.end.line)
                               (and (= a.range.end.line b.range.end.line)
                                   (or (< a.range.end.character b.range.end.character)
                                       (= a.range.end.character b.range.end.character)))))))))))

(fn check [file-contents]
  (let [{: self : uri : cursor : locations} (create-client-with-files file-contents)
        [response] (self:references uri cursor)]
    (if (not= null response.result)
      (do
        (table.sort locations location-comparator)
        (table.sort response.result location-comparator)
        (faith.= locations response.result
                 (view file-contents)))
      (faith.= locations []))))

(fn test-references []
  (check "(let [x 10] ==x==|)")
  (check "(let [x| 10] ==x==)")
  (check "(let [x| 10] ==x== ==x== ==x==)")
  (check "(fn x []) ==x|==")
  (check "(fn x []) ==|x==")
  (check "(fn x| []) ==x==")
  (check "(fn x [])| x")
  (check "(let [x nil] ==|x.y== ==x.z==)")
  (check "(let [x nil] ==x|.y== ==x.z==)")
  (check "(let [x nil] x.|y x.z)")
  (check "(let [x nil] x.y| x.z)")
  (check "(let [x| 10]
            (print ==x==)
            (let [x :shadowed] x))")
  nil)

{: test-references}
