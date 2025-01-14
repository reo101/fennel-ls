(local faith (require :faith))
(local {: view} (require :fennel))
(local {: create-client-with-files} (require :test.utils))
(local {: apply-edits} (require :fennel-ls.utils))

(create-client-with-files "(print :hi)")

(fn check [file-contents action-I-want-to-take desired-file-contents]
  (let [{: self : uri :locations [range] : encoding : text} (create-client-with-files file-contents)
        [{:result responses}] (self:code-action uri range.range)
        action (accumulate [result nil
                            _ action (ipairs responses) &until result]
                 (if (= action.title action-I-want-to-take)
                   action))]
    (if (not action)
      (error
         (.. "I couldn't find your action \"" action-I-want-to-take "\" in:
"
             (view (icollect [_ action (ipairs responses)]
                     action.title)))))
    (let [edits (?. action :edit :changes uri)
          edited-text (apply-edits text edits encoding)]
      (faith.= desired-file-contents edited-text))))

(fn test-fix-op-no-arguments []
  (check "(let [x (+====)]
            (print x))"
         "op-with-no-arguments"
         "(let [x 0]
            (print x))"))

; (fn test-fix-method-function []
;   (check "(local x {})
;           (fn x:y [a b c]
;             (print self a b c))"
;          "TO-BE-NAMED"
;          "(local x {})
;           (fn x.y [self a b c]
;             (print self a b c))"))

{: test-fix-op-no-arguments}
