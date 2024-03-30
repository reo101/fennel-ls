"Util
A collection of utility functions. Many of these convert data between a
Language-Server-Protocol representation and a Lua representation.
These functions are all pure functions, which makes me happy."

(λ next-line [str ?from]
  "Find the start of the next line from a given byte offset, or from the start of the string."
  (let [from (or ?from 1)]
    (case (str:find "[\r\n]" from)
      i (+ i (length (str:match "\r?\n?" i)))
      nil nil)))

(λ next-lines [str nlines ?from]
  "Find the start of the next line from a given byte offset, or from the start of the string."
  (faccumulate [from (or ?from 1)
                _ 1 nlines]
    (next-line str from)))

(fn utf [byte]
  "returns the number of (utf8) bytes, and (utf-16) code units from the first byte of a character"
  (if
    (<= 0x00 byte 0x80)
    (values 1 1)
    (<= 0xC0 byte 0xDF)
    (values 2 1)
    (<= 0xE0 byte 0xEF)
    (values 3 1)
    (<= 0xF0 byte 0xF7)
    (values 4 2)
    (error :utf8-error)))

(fn byte->unit16 [str ?byte]
  "convert from normal units to utf16 garbage"
  ;; TODO reconsider this when upstream #180 is fixed
  (let [unit8 (math.min (length str) ?byte)]
    (var o8 0)
    (var o16 0)
    (while (< o8 unit8)
      (let [(a8 a16) (utf (str:byte (+ 1 o8)))]
        (set o8 (+ o8 a8))
        (set o16 (+ o16 a16))))
    (if (= o8 unit8)
      o16
      (error :utf8-error))))


(fn unit16->byte [str unit16]
  "convert from utf16 garbage to normal units"
  (var o8 0)
  (var o16 0)
  (while (< o16 unit16)
    (let [(a8 a16) (utf (str:byte (+ 1 o8)))]
      (set o8 (+ o8 a8))
      (set o16 (+ o16 a16))))
  (if (= o16 unit16)
    o8
    (error :utf8-error)))

(λ pos->position [str line character encoding]
  (case encoding
    :utf-8 {: line : character}
    :utf-16 (let [pos (next-lines str line)]
              {: line
               :character (byte->unit16 (str:sub pos) character)})
    _ (error (.. "unknown encoding: " encoding))))

(λ byte->position [str byte encoding]
  "take a 1-indexed byte, and convert it to an LSP position based on the given encoding"
  (var line 0)
  (var pos 1)
  (while (let [npos (next-line str pos)]
           (when (and npos (<= npos byte))
             (set pos npos)
             (set line (+ line 1))
             true)))
  (case encoding
    :utf-8 {: line :character (- byte pos)}
    :utf-16 {: line :character (byte->unit16 (str:sub pos) (- byte pos))}
    _ (error (.. "unknown encoding: " encoding))))

(λ position->byte [str {: line : character} encoding]
  "take an LSP position and convert it to a 1-indexed byte based on the given encoding"
  (let [pos (next-lines str line)]
    (assert pos :bad-pos)
    (case encoding
      :utf-8 (+ pos character)
      :utf-16 (+ pos (unit16->byte (str:sub pos) character))
      _ (error (.. "unknown encoding: " encoding)))))

(λ startswith [str pre]
  (let [len (length pre)]
    (= (str:sub 1 len) pre)))

(λ uri->path [uri]
  "Strips the \"file://\" prefix from a uri to turn it into a path. Throws an error if it is not a path uri"
  (local prefix "file://")
  (assert (startswith uri prefix) "encountered a URI that is not a file???")
  (string.sub uri (+ (length prefix) 1)))

(λ path->uri [path]
  "Prepents the \"file://\" prefix to a path to turn it into a uri"
  (.. "file://" path))

(λ replace [text start-position end-position replacement encoding]
  "Replaces a range of text with a replacement, using the protocol's definition of range."
  (let [start (position->byte text start-position encoding)
        end   (position->byte text end-position   encoding)]
    (..
      (text:sub 1 (- start 1))
      replacement
      (text:sub end))))

(λ apply-changes [initial-text changes encoding]
  "Takes a list of Language-Server-Protocol `contentChanges` and applies them to a piece of text."
  (accumulate
    [contents initial-text
     _ change (ipairs changes)]
    (case change
      ;; Handle a change
      {:range {: start : end} : text}
      (replace contents start end text encoding)
      ;; A replacement of the entire body
      {: text}
      text)))

(λ apply-edits [initial-text edits encoding]
  "Takes a list of Language-Server-Protocol `TextEdit` or `AnnotatedTextEdit` and applies them to a piece of text.

WARNING: this is only used in the test code, not in the real language server"
  (accumulate
    [contents initial-text
     _ edit (ipairs edits)]
    (case edit
      ;; Handle a change
      {:range {: start : end} : newText}
      (replace contents start end newText encoding))))

(λ get-ast-info [ast info]
  "gets `info` from ast if possible"
  (if (= :number (type ast))
    nil
    ;; find a given key of info from an AST object
    (or (?. (getmetatable ast) info)
        (?. ast info))))

(fn multi-sym-split [symbol ?offset]
  (local symbol (tostring symbol))
  (if (or (= symbol ".")
          (= symbol "..")
          (= symbol "...")
          (= symbol ":")
          (= symbol "?."))
    [symbol]
    (let [offset (or ?offset (length symbol))
          next-separator (or (symbol:find ".[.:]" offset)
                             (length symbol))
          symbol (symbol:sub 1 next-separator)]
      (icollect [word (: (.. symbol ".") :gmatch "(.-)[.:]")]
        word))))

(fn multi-sym-base [symbol]
  (if (or (= symbol ".")
          (= symbol "..")
          (= symbol "...")
          (= symbol ":")
          (= symbol "?."))
    (tostring symbol)
    (pick-values 1 (: (tostring symbol) :match "[^.:]*"))))

(λ type= [val typ]
  (= (type val) typ))

(λ uniq-by [list eq?]
  "I know the big O of this is bad, but we'll come back to it if it's a performance problem"
  (let [result []]
    (each [_ new-item (ipairs list)]
      (if (not (accumulate [any? nil
                            _ seen-item (ipairs result)
                            &until any?]
                 (eq? seen-item new-item)))
        (table.insert result new-item)))
    result))

(λ split-spaces [str]
  (icollect [m (str:gmatch "[^ ]+")]
    m))

(λ eprintln [?tbl]
  "Pretty-print a table on stderr, used for debugging"
  (let [inspect (require :inspect)]
    (io.stderr:write
      (string.format
        "%s\n"
        (inspect ?tbl)))))

{: uri->path
 : path->uri
 : pos->position
 : byte->position
 : position->byte
 : apply-changes
 : apply-edits
 : multi-sym-split
 : multi-sym-base
 : get-ast-info
 : uniq-by
 : type=
 : split-spaces
 : eprintln}
