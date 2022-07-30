(local fennel (require :fennel))
(local dispatch (require :fennel-ls.dispatch))
(local json-rpc (require :fennel-ls.json-rpc))
(local {: log} (require :fennel-ls.log))

(λ main-loop [in out]
  (local send #(json-rpc.write out $))
  (local state [])
  (while true
    (let [msg (json-rpc.read in)]
      (log msg)
      (dispatch.handle state send msg))))

(λ main []
  (main-loop
    (io.input)
    (io.output)))

(main)
