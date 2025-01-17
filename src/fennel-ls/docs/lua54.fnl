"Lua 5.4 Documentation of globals.
I wish these were generated, but I did them by hand:

Pandoc converted the reference file to .md, and I manually sliced up
and edited the markdown into this page."

(local {: sym} (require :fennel))
(local docs
  {:_G {:metadata {:fnl/docstring "A global variable (not a function) that holds the global environment. Lua and Fennel do not use this variable; changing its value does not affect any environment, nor vice versa."}}
   :_VERSION {:metadata {:fnl/docstring "A global variable (not a function) that holds a string containing the running Lua version. The current value of this variable is `Lua 5.4`."}}
   :arg {:metadata {:fnl/docstring "A global variable (not a function) that holds the command line arguments."}}
   :assert {:metadata {:fnl/arglist [:v :?message]
                       :fnl/docstring "Raises an error if the value of its argument `v` is false (i.e., **nil**
or **false**); otherwise, returns all its arguments. In case of error,
`?message` is the error object; when absent, it defaults to
\"`assertion failed!`\""}}
   :collectgarbage {:metadata {:fnl/arglist [:?opt :?arg]
                               :fnl/docstring "This function is a generic interface to the garbage collector. It
performs different functions according to its first argument, `opt`:

-   **\"`collect`\":** Performs a full garbage-collection cycle. This is
    the default option.
-   **\"`stop`\":** Stops automatic execution of the garbage collector.
    The collector will run only when explicitly invoked, until a call to
    restart it.
-   **\"`restart`\":** Restarts automatic execution of the garbage
    collector.
-   **\"`count`\":** Returns the total memory in use by Lua in Kbytes.
    The value has a fractional part, so that it multiplied by 1024 gives
    the exact number of bytes in use by Lua.
-   **\"`step`\":** Performs a garbage-collection step. The step
    \"size\" is controlled by `arg`. With a zero value, the collector
    will perform one basic (indivisible) step. For non-zero values, the
    collector will perform as if that amount of memory (in Kbytes) had
    been allocated by Lua. Returns **true** if the step finished a
    collection cycle.
-   **\"`isrunning`\":** Returns a boolean that tells whether the
    collector is running (i.e., not stopped).
-   **\"`incremental`\":** Change the collector mode to incremental.
    This option can be followed by three numbers: the garbage-collector
    pause, the step multiplier, and the step size (see
    [§2.5.1](https://lua.org/manual/5.4/manual.html#2.5.1)). A zero means
    to not change that value.
-   **\"`generational`\":** Change the collector mode to generational.
    This option can be followed by two numbers: the garbage-collector
    minor multiplier and the major multiplier (see
    [§2.5.2](https://lua.org/manual/5.4/manual.html#2.5.2)). A zero means
    to not change that value.

See [§2.5](https://lua.org/manual/5.4/manual.html#2.5) for more details
about garbage collection and some of these options.

This function should not be called by a finalizer."}}
   :coroutine
   {:metadata {:fnl/docstring "This library comprises the operations to manipulate coroutines, which come inside the table coroutine. See §2.6 for a general description of coroutines."}
    :fields
    {:close {:metadata {:fnl/arglist [:co] :fnl/docstring
                        "Closes coroutine `co`,
that is,
closes all its pending to-be-closed variables
and puts the coroutine in a dead state.
The given coroutine must be dead or suspended.
In case of error
(either the original error that stopped the coroutine or
errors in closing methods),
returns `false` plus the error object;
otherwise returns `true`."}}
     :create {:metadata {:fnl/arglist [:f] :fnl/docstring
                         "Creates a new coroutine, with body `f`.
`f` must be a function.
Returns this new coroutine,
an object with type `\"thread\"`."}}
     :isyieldable {:metadata {:fnl/arglist [:?co] :fnl/docstring
                              "Returns `true` when the coroutine `?co` can yield.
The default for `?co` is the running coroutine.

A coroutine is yieldable if it is not the main thread and
it is not inside a non-yieldable C function."}}
     :resume {:metadata {:fnl/arglist [:co :?val1 :...] :fnl/docstring
                         "Starts or continues the execution of coroutine `co`.
The first time you resume a coroutine,
it starts running its body.
The values `?val1`, ... are passed
as the arguments to the body function.
If the coroutine has yielded,
`resume` restarts it;
the values `?val1`, ... are passed
as the results from the yield.

If the coroutine runs without any errors,
`resume` returns `true` plus any values passed to `yield`
(when the coroutine yields) or any values returned by the body function
(when the coroutine terminates).
If there is any error,
`resume` returns `false` plus the error message."}}
     :running {:metadata {:fnl/arglist [] :fnl/docstring
                          "Returns the running coroutine plus a boolean,
`true` when the running coroutine is the main one."}}
     :status {:metadata {:fnl/arglist [:?co] :fnl/docstring
                         "Returns the status of the coroutine `?co`, as a string:
`\"running\"`,
if the coroutine is running
(that is, it is the one that called `status`);
`\"suspended\"`, if the coroutine is suspended in a call to `yield`,
or if it has not started running yet;
`\"normal\"` if the coroutine is active but not running
(that is, it has resumed another coroutine);
and `\"dead\"` if the coroutine has finished its body function,
or if it has stopped with an error.

The default for `?co` is the running coroutine."}}
     :wrap {:metadata {:fnl/arglist [:?f] :fnl/docstring
                       "Creates a new coroutine, with body `f`;
`f` must be a function.
Returns a function that resumes the coroutine each time it is called.
Any arguments passed to this function behave as the
extra arguments to `resume`.
The function returns the same values returned by `resume`,
except the first boolean.
In case of error,
the function closes the coroutine and propagates the error."}}
     :yield {:metadata {:fnl/arglist [:...] :fnl/docstring
                        "Suspends the execution of the calling coroutine.
Any arguments to `yield` are passed as extra results to `resume`."}}}}
   :debug
   {:metadata {:fnl/docstring "This library provides the functionality of the debug interface to Lua programs. You should exert care when using this library. Several of its functions violate basic assumptions about Lua code (e.g., that variables local to a function cannot be accessed from outside; that userdata metatables cannot be changed by Lua code; that Lua programs do not crash) and therefore can compromise otherwise secure code. Moreover, some functions in this library may be slow.

 All functions that operate over a thread have an optional first argument which is the thread to operate over. The default is always the current thread."}
    :fields
    {:debug {:metadata {:fnl/arglist [] :fnl/docstring
                        "Enters an interactive mode with the user,
running each string that the user enters.
Using simple commands and other debug facilities,
the user can inspect global and local variables,
change their values, evaluate expressions, and so on.
A line containing only the word `cont` finishes this function,
so that the caller continues its execution.

Note that commands for `debug.debug` are not lexically nested
within any function and so have no direct access to local variables."}}
     :gethook {:metadata {:fnl/arglist [:?thread] :fnl/docstring
                          "Returns the current hook settings of the thread, as three values:
the current hook function, the current hook mask,
and the current hook count,
as set by the `debug.sethook` function.

Returns `fail` if there is no active hook."}}
     :getinfo {:metadata {:fnl/arglist [:f :?what] :fnl/docstring
                          "Returns a table with information about a function.
You can give the function directly
or you can give a number as the value of `f`,
which means the function running at level `f` of the call stack
of the given thread:
level 0 is the current function (`getinfo` itself);
level 1 is the function that called `getinfo`
(except for tail calls, which do not count in the stack);
and so on.
If `f` is a number greater than the number of active functions,
then `getinfo` returns `fail`.

The returned table can contain all the fields returned by `lua_getinfo`,
with the string `what` describing which fields to fill in.
The default for `what` is to get all information available,
except the table of valid lines.
If present,
the option '`f`'
adds a field named `func` with the function itself.
If present,
the option '`L`'
adds a field named `activelines` with the table of
valid lines.

For instance, the expression `(. (debug.getinfo 1 \"n\") :name)` returns
a name for the current function,
if a reasonable name can be found,
and the expression `(debug.getinfo print)`
returns a table with all available information
about the `print` function."}}
     :getlocal {:metadata {:fnl/arglist [:f :local] :fnl/docstring
                           "This function returns the name and the value of the local variable
with index `local` of the function at level `f` of the stack.
This function accesses not only explicit local variables,
but also parameters and temporary values.

The first parameter or local variable has index 1, and so on,
following the order that they are declared in the code,
counting only the variables that are active
in the current scope of the function.
Compile-time constants may not appear in this listing,
if they were optimized away by the compiler.
Negative indices refer to vararg arguments;
-1 is the first vararg argument.
The function returns `fail`
if there is no variable with the given index,
and raises an error when called with a level out of range.
(You can call `debug.getinfo` to check whether the level is valid.)

Variable names starting with `'('` (open parenthesis)
represent variables with no known names
(internal variables such as loop control variables,
and variables from chunks saved without debug information).

The parameter `f` may also be a function.
In that case, `getlocal` returns only the name of function parameters."}}
     :getmetatable {:metadata {:fnl/arglist [:value] :fnl/docstring
                               "Returns the metatable of the given `value`
or `nil` if it does not have a metatable."}}
     :getregistry {:metadata {:fnl/arglist [] :fnl/docstring
                              "Returns the registry table."}}
     :getupvalue {:metadata {:fnl/arglist [:f :up] :fnl/docstring
                             "This function returns the name and the value of the upvalue
with index `up` of the function `f`.
The function returns `fail`
if there is no upvalue with the given index.

(For Lua functions,
upvalues are the external local variables that the function uses,
and that are consequently included in its closure.)

For C functions, this function uses the empty string `\"\"`
as a name for all upvalues.

Variable name '`?`' (interrogation mark)
represents variables with no known names
(variables from chunks saved without debug information)."}}
     :getuservalue {:metadata {:fnl/arglist [:u :n] :fnl/docstring
                               "Returns the `n`-th user value associated
to the userdata `u` plus a boolean,
`false` if the userdata does not have that value."}}
     :sethook {:metadata {:fnl/arglist [:hook :mask :?count] :fnl/docstring
                          "Sets the given function as the debug hook.
The string `mask` and the number `?count` describe
when the hook will be called.
The string mask may have any combination of the following characters,
with the given meaning:

* `c`: the hook is called every time Lua calls a function;
* `r`: the hook is called every time Lua returns from a function;
* `l`:  the hook is called every time Lua enters a new line of code.

Moreover,
with a `?count` different from zero,
the hook is called also after every `?count` instructions.

When called without arguments,
`debug.sethook` turns off the hook.

When the hook is called, its first parameter is a string
describing the event that has triggered its call:
`\"call\"`, `\"tail call\"`, `\"return\"`,
`\"line\"`, and `\"count\"`.
For line events,
the hook also gets the new line number as its second parameter.
Inside a hook,
you can call `getinfo` with level 2 to get more information about
the running function.
(Level 0 is the `getinfo` function,
and level 1 is the hook function.)"}}
     :setlocal {:metadata {:fnl/arglist [:level :local :value] :fnl/docstring
                           "This function assigns the value `value` to the local variable
with index `local` of the function at level `level` of the stack.
The function returns `fail` if there is no local
variable with the given index,
and raises an error when called with a `level` out of range.
(You can call `getinfo` to check whether the level is valid.)
Otherwise, it returns the name of the local variable.

See `debug.getlocal` for more information about
variable indices and names."}}
     :setmetatable {:metadata {:fnl/arglist [:value :table] :fnl/docstring
                               "Sets the metatable for the given `value` to the given `table`
(which can be `nil`).
Returns `value`."}}
     :setupvalue {:metadata {:fnl/arglist [:f :up :value] :fnl/docstring
                             "This function assigns the value `value` to the upvalue
with index `up` of the function `f`.
The function returns `fail` if there is no upvalue
with the given index.
Otherwise, it returns the name of the upvalue.

See `debug.getupvalue` for more information about upvalues."}}
     :setuservalue {:metadata {:fnl/arglist [:udata :value :n] :fnl/docstring
                               "Sets the given `value` as
the `n`-th user value associated to the given `udata`.
`udata` must be a full userdata.

Returns `udata`,
or `fail` if the userdata does not have that value."}}
     :traceback {:metadata {:fnl/arglist [:?message :?level] :fnl/docstring
                            "If `?message` is present but is neither a string nor `nil`,
this function returns `?message` without further processing.
Otherwise,
it returns a string with a traceback of the call stack.
The optional `?message` string is appended
at the beginning of the traceback.
An optional `?level` number tells at which level
to start the traceback
(default is 1, the function calling `traceback`)."}}
     :upvalueid {:metadata {:fnl/arglist [:f :n] :fnl/docstring
                            "Returns a unique identifier (as a light userdata)
for the upvalue numbered `n`
from the given function.

These unique identifiers allow a program to check whether different
closures share upvalues.
Lua closures that share an upvalue
(that is, that access a same external local variable)
will return identical ids for those upvalue indices."}}}}
   :dofile {:metadata {:fnl/arglist [:?filename]
                       :fnl/docstring "Opens the named file and executes its content as a Lua chunk. When
called without arguments, `dofile` executes the content of the standard
input (`stdin`). Returns all values returned by the chunk. In case of
errors, `dofile` propagates the error to its caller. (That is, `dofile`
does not run in protected mode.)"}}
   :error {:metadata {:fnl/arglist [:message :?level]
                      :fnl/docstring "Raises an error (see [§2.3](https://lua.org/manual/5.4/manual.html#2.3)) with `message` as the error object.
This function never returns.

Usually, `error` adds some information about the error position at the
beginning of the message, if the message is a string. The `level`
argument specifies how to get the error position. With level 1 (the
default), the error position is where the `error` function was called.
Level 2 points the error to where the function that called `error` was
called; and so on. Passing a level 0 avoids the addition of error
position information to the message."}}
   :getmetatable {:metadata {:fnl/arglist [:object]
                             :fnl/docstring "If `object` does not have a metatable, returns **nil**. Otherwise, if
the object\'s metatable has a `__metatable` field, returns the
associated value. Otherwise, returns the metatable of the given object."}}
   :io
   {:metadata {:fnl/docstring "The I/O library provides two different styles for file manipulation. The first one uses implicit file handles; that is, there are operations to set a default input file and a default output file, and all input/output operations are done over these default files. The second style uses explicit file handles."}
    :fields
    {:close {:metadata {:fnl/arglist [:?file] :fnl/docstring
                        "Closes `?file`.
Note that files are automatically closed when
their handles are garbage collected,
but that takes an unpredictable amount of time to happen.

When closing a file handle created with `io.popen`,
`io.close` returns the same values
returned by `os.execute.
Without a `?file`, closes the default output file."}}
     :flush {:metadata {:fnl/arglist [:?file] :fnl/docstring
                        "Saves any written data to `?file`."}}
     :input {:metadata {:fnl/arglist [:?file] :fnl/docstring
                        "When called with a file name, it opens the named file (in text mode),
and sets its handle as the default input file.
When called with a file handle,
it simply sets this file handle as the default input file.
When called without arguments,
it returns the current default input file.

In case of errors this function raises the error,
instead of returning an error code."}}
     :lines {:metadata {:fnl/arglist [:?filename :...] :fnl/docstring
                        "Opens the given file name in read mode
and returns an iterator function that
works like `(file:lines ...)` over the opened file.
When the iterator function fails to read any value,
it automatically closes the file.
Besides the iterator function,
`io.lines` returns three other values:
two `nil` values as placeholders,
plus the created file handle.
Therefore, when used in a generic `for` loop,
the file is closed also if the loop is interrupted by an
error or a `break`.

The call `(io.lines)` (with no file name) is equivalent
to `(: (io.input) :lines \"l\")`;
that is, it iterates over the lines of the default input file.
In this case, the iterator does not close the file when the loop ends.

In case of errors opening the file,
this function raises the error,
instead of returning an error code."}}
     :open {:metadata {:fnl/arglist [:filename :?mode] :fnl/docstring
                       "This function opens a file,
in the mode specified in the string `?mode`.
In case of success,
it returns a new file handle.

The `?mode` string can be any of the following:

* `\"r\"`:  read mode (the default);
* `\"w\"`:  write mode;
* `\"a\"`:  append mode;
* `\"r+\"`:  update mode, all previous data is preserved;
* `\"w+\"`:  update mode, all previous data is erased;
* `\"a+\"`:  append update mode, previous data is preserved,
  writing is only allowed at the end of file.

The `?mode` string can also have a '`b`' at the end,
which is needed in some systems to open the file in binary mode."}}
     :output {:metadata {:fnl/arglist [:?file] :fnl/docstring
                         "Similar to `io.input`, but operates over the default output file."}}
     :popen {:metadata {:fnl/arglist [:prog :?mode] :fnl/docstring
                        "This function is system dependent and is not available
on all platforms.

Starts the program `prog` in a separated process and returns
a file handle that you can use to read data from this program
(if `?mode` is `\"r\"`, the default)
or to write data to this program
(if `?mode` is `\"w\"`)."}}
     :read {:metadata {:fnl/arglist [:...] :fnl/docstring
                       "Reads from `(io.input)`,
according to the given formats, which specify what to read.
For each format,
the function returns a string or a number with the characters read,
or `fail` if it cannot read data with the specified format.
(In this latter case,
the function does not read subsequent formats.)
When called without arguments,
it uses a default format that reads the next line
(see below).

The available formats are

* `\"n\"`:
    reads a numeral and returns it as a float or an integer,
    following the lexical conventions of Lua.
    (The numeral may have leading whitespaces and a sign.)
    This format always reads the longest input sequence that
    is a valid prefix for a numeral;
    if that prefix does not form a valid numeral
    (e.g., an empty string, \"`0x`\", or \"`3.4e-`\")
    or it is too long (more than 200 characters),
    it is discarded and the format returns `fail`.
* `\"a\"`:
    reads the whole file, starting at the current position.
    On end of file, it returns the empty string;
    this format never fails.
* `\"l\"`:
    reads the next line skipping the end of line,
    returning `fail` on end of file.
    This is the default format.
* `\"L\"`:
    reads the next line keeping the end-of-line character (if present),
    returning `fail` on end of file.
* number:
    reads a string with up to this number of bytes,
    returning `fail` on end of file.
    If `number` is zero,
    it reads nothing and returns an empty string,
    or `fail` on end of file.

The formats \"`l`\" and \"`L`\" should be used only for text files."}}
     :tmpfile {:metadata {:fnl/arglist [] :fnl/docstring
                          "In case of success,
returns a handle for a temporary file.
This file is opened in update mode
and it is automatically removed when the program ends."}}
     :type {:metadata {:fnl/arglist [:obj] :fnl/docstring
                       "Checks whether `obj` is a valid file handle.
Returns the string `\"file\"` if `obj` is an open file handle,
`\"closed file\"` if `obj` is a closed file handle,
or `fail` if `obj` is not a file handle."}}
     :write {:metadata {:fnl/arglist [:...] :fnl/docstring
                        "Writes the value of each of its arguments to `(io.output)`.
The arguments must be strings or numbers.

In case of success, this function returns `file`."}}}}
   :ipairs {:metadata {:fnl/arglist [:t]
                       :fnl/docstring  "Returns three values (an iterator function, the table `t`, and 0) so
that the construction

```fnl
(each [i v (ipairs t)] <body>)
```

will iterate over the key--value pairs `(values 1 (. t 1))`, `(values 2 (. t 2))`, `...`, up
to the first absent index."}}
   :load {:metadata {:fnl/arglist [:chunk :?chunkname :?mode :?env]
                     :fnl/docstring "Loads a chunk.

If `chunk` is a string, the chunk is this string. If `chunk` is a
function, `load` calls it repeatedly to get the chunk pieces. Each call
to `chunk` must return a string that concatenates with previous results.
A return of an empty string, **nil**, or no value signals the end of the
chunk.

If there are no syntactic errors, `load` returns the compiled chunk as a
function; otherwise, it returns **fail** plus the error message.

When you load a main chunk, the resulting function will always have
exactly one upvalue, the `_ENV` variable (see
[§2.2](https://lua.org/manual/5.4/manual.html#2.2)). However, when you
load a binary chunk created from a function (see
[`string.dump`](https://lua.org/manual/5.4/manual.html#pdf-string.dump)),
the resulting function can have an arbitrary number of upvalues, and there
is no guarantee that its first upvalue will be the `_ENV` variable. (A
non-main function may not even have an `_ENV` upvalue.)

Regardless, if the resulting function has any upvalues, its first
upvalue is set to the value of `env`, if that parameter is given, or to
the value of the global environment. Other upvalues are initialized with
**nil**. All upvalues are fresh, that is, they are not shared with any
other function.

`chunkname` is used as the name of the chunk for error messages and debug
information (see [§4.7](https://lua.org/manual/5.4/manual.html#4.7)). When
absent, it defaults to `chunk`, if `chunk` is a string, or to
\"`=(load)`\" otherwise.

The string `mode` controls whether the chunk can be text or binary (that
is, a precompiled chunk). It may be the string \"`b`\" (only binary
chunks), \"`t`\" (only text chunks), or \"`bt`\" (both binary and text).
The default is \"`bt`\".

It is safe to load malformed binary chunks; `load` signals an
appropriate error. However, Lua does not check the consistency of the
code inside binary chunks; running maliciously crafted bytecode can
crash the interpreter."}}
   :loadfile {:metadata {:fnl/arglist [:filename :?mode :?env]
                         :fnl/docstring "Similar to [`load`](https://lua.org/manual/5.4/manual.html#pdf-load), but
gets the chunk from file `filename` or from the standard input, if no file
name is given."}}
   :math
   {:metadata {:fnl/docstring "This library provides basic mathematical functions. It provides all its functions and constants inside the table `math`. Functions with the annotation `\"integer/float\"` give integer results for integer arguments and float results for non-integer arguments. The rounding functions `math.ceil`, `math.floor`, and `math.modf` return an integer when the result fits in the range of an integer, or a float otherwise."}
    :fields
    {:abs {:metadata {:fnl/arglist [:x] :fnl/docstring
                      "Returns the maximum value between `x` and `-x`. (integer/float)"}}
     :acos {:metadata {:fnl/arglist [:x] :fnl/docstring
                       "Returns the arc cosine of `x` (in radians)."}}
     :asin {:metadata {:fnl/arglist [:x] :fnl/docstring
                       "Returns the arc sine of `x` (in radians)."}}
     :atan {:metadata {:fnl/arglist [:y :?x] :fnl/docstring
                       "Returns the arc tangent of `(/ y ?x)` (in radians),
using the signs of both arguments to find the
quadrant of the result.
It also handles correctly the case of `?x` being zero.

The default value for `?x` is 1,
so that the call `(math.atan y)`
returns the arc tangent of `y`."}}
     :ceil {:metadata {:fnl/arglist [:x] :fnl/docstring
                       "Returns the smallest integral value greater than or equal to `x`."}}
     :cos {:metadata {:fnl/arglist [:x] :fnl/docstring
                      "Returns the cosine of `x` (assumed to be in radians)."}}
     :deg {:metadata {:fnl/arglist [:x] :fnl/docstring
                      "Converts the angle `x` from radians to degrees."}}
     :exp {:metadata {:fnl/arglist [:x] :fnl/docstring
                      "Returns the value (^ e x)
(where `e` is the base of natural logarithms)."}}
     :floor {:metadata {:fnl/arglist [:x] :fnl/docstring
                        "Returns the largest integral value less than or equal to `x`."}}
     :fmod {:metadata {:fnl/arglist [:x :y] :fnl/docstring
                       "Returns the remainder of the division of `x` by `y`
that rounds the quotient towards zero. (integer/float)"}}
     :huge {:metadata {:fnl/docstring
                       "The float value `HUGE_VAL`,
a value greater than any other numeric value."}}
     :log {:metadata {:fnl/arglist [:x :?base] :fnl/docstring
                      "Returns the logarithm of `x` in the given base.
The default for `?base` is `e`
(so that the function returns the natural logarithm of `x`)."}}
     :max {:metadata {:fnl/arglist [:x :...] :fnl/docstring
                      "Returns the argument with the maximum value,
according to the Lua operator `<`."}}
     :maxinteger {:metadata {:fnl/docstring
                             "An integer with the maximum value for an integer."}}
     :min {:metadata {:fnl/arglist [:x :...] :fnl/docstring
                      "Returns the argument with the minimum value,
according to the Lua operator `<`."}}
     :mininteger {:metadata {:fnl/docstring
                             "An integer with the minimum value for an integer."}}
     :modf {:metadata {:fnl/arglist [:x] :fnl/docstring
                       "Returns the integral part of `x` and the fractional part of `x`.
Its second result is always a float."}}
     :pi {:metadata {:fnl/docstring
                     "The value of `pi`."}}
     :rad {:metadata {:fnl/arglist [:x] :fnl/docstring
                      "Converts the angle `x` from degrees to radians."}}
     :random {:metadata {:fnl/arglist [:?m :?n] :fnl/docstring
                         "When called without arguments,
returns a pseudo-random float with uniform distribution
in the range  `[0,1)`.
When called with two integers `m` and `n`,
`math.random` returns a pseudo-random integer
with uniform distribution in the range `[m, n]`
The call `(math.random n)`, for a positive `n`,
is equivalent to `(math.random 1 n)`.
The call `(math.random 0)` produces an integer with
all bits (pseudo)random.

This function uses the `xoshiro256**` algorithm to produce
pseudo-random 64-bit integers,
which are the results of calls with argument 0.
Other results (ranges and floats)
are unbiased extracted from these integers.

Lua initializes its pseudo-random generator with the equivalent of
a call to `math.randomseed` with no arguments,
so that `math.random` should generate
different sequences of results each time the program runs."}}
     :randomseed {:metadata {:fnl/arglist [:?x :?y] :fnl/docstring
                             "When called with at least one argument,
the integer parameters `x` and `y` are
joined into a 128-bit `seed` that
is used to reinitialize the pseudo-random generator;
equal seeds produce equal sequences of numbers.
The default for `y` is zero.

When called with no arguments,
Lua generates a seed with
a weak attempt for randomness.

This function returns the two seed components
that were effectively used,
so that setting them again repeats the sequence.

To ensure a required level of randomness to the initial state
(or contrarily, to have a deterministic sequence,
for instance when debugging a program),
you should call `math.randomseed` with explicit arguments."}}
     :sin {:metadata {:fnl/arglist [:x] :fnl/docstring
                      "Returns the sine of `x` (assumed to be in radians)."}}
     :sqrt {:metadata {:fnl/arglist [:x] :fnl/docstring
                       "Returns the square root of `x`.
(You can also use the expression `(^ x 0.5)` to compute this value.)"}}
     :tan {:metadata {:fnl/arglist [:x] :fnl/docstring
                      "Returns the tangent of `x` (assumed to be in radians)."}}
     :tointeger {:metadata {:fnl/arglist [:x] :fnl/docstring
                            "If the value `x` is convertible to an integer,
returns that integer.
Otherwise, returns `fail`."}}
     :type {:metadata {:fnl/arglist [:x] :fnl/docstring
                       "Returns \"`integer`\" if `x` is an integer,
\"`float`\" if it is a float,
or `fail` if `x` is not a number."}}
     :ult {:metadata {:fnl/arglist [:m :n] :fnl/docstring
                      "Returns a boolean,
`true` if and only if integer `m` is below integer `n` when
they are compared as unsigned integers."}}}}
   :next {:metadata {:fnl/arglist [:table :?index]
                     :fnl/docstring "Allows a program to traverse all fields of a table. Its first argument
is a table and its second argument is an index in this table. A call to
`next` returns the next index of the table and its associated value.
When called with **nil** as its second argument, `next` returns an
initial index and its associated value. When called with the last index,
or with **nil** in an empty table, `next` returns **nil**. If the second
argument is absent, then it is interpreted as **nil**. In particular,
you can use `(next t)` to check whether a table is empty.

The order in which the indices are enumerated is not specified, *even
for numeric indices*. (To traverse a table in numerical order, use **for**.)

You should not assign any value to a non-existent field in a table
during its traversal. You may however modify existing fields. In
particular, you may set existing fields to **nil**."}}
   :os
   {:metadata {:fnl/docstring "Operating System Facilities"}
    :fields
    {:clock {:metadata {:fnl/arglist [] :fnl/docstring
                        "Returns an approximation of the amount in seconds of CPU time
used by the program,
as returned by the underlying ISO C function `clock`."}}
     :date {:metadata {:fnl/arglist [:?format :?time] :fnl/docstring
                       "Returns a string or a table containing date and time,
formatted according to the given string `format`.

If the `time` argument is present,
this is the time to be formatted
(see the `os.time` function for a description of this value).
Otherwise, `date` formats the current time.

If `format` starts with '`!`',
then the date is formatted in Coordinated Universal Time.
After this optional character,
if `format` is the string `\"*t\"`,
then `date` returns a table with the following fields:
`year`, `month` (1 - 12), `day` (1 - 31),
`hour` (0 - 23), `min` (0 - 59),
`sec` (0 - 61, due to leap seconds),
`wday` (weekday, 1 - 7, Sunday is 1),
`yday` (day of the year, 1 - 366),
and `isdst` (daylight saving flag, a boolean).
This last field may be absent
if the information is not available.

If `format` is not \"`*t`\",
then `date` returns the date as a string,
formatted according to the same rules as the ISO C function `strftime`.

If `format` is absent, it defaults to \"`%c`\",
which gives a human-readable date and time representation
using the current locale.

On non-POSIX systems,
this function may be not thread safe
because of its reliance on C function `gmtime` and C function `localtime`."}}
     :difftime {:metadata {:fnl/arglist [:t2 :t1] :fnl/docstring
                           "Returns the difference, in seconds,
from time `t1` to time `t2`
(where the times are values returned by `os.time`).
In POSIX, Windows, and some other systems,
this value is exactly `t2 - t1`."}}
     :execute {:metadata {:fnl/arglist [:?command] :fnl/docstring
                          "This function is equivalent to the ISO C function `system`.
It passes `command` to be executed by an operating system shell.
Its first result is `true`
if the command terminated successfully,
or `fail` otherwise.
After this first result
the function returns a string plus a number,
as follows:

* `\"exit\"`:
    the command terminated normally;
    the following number is the exit status of the command.

* `\"signal\"`:
    the command was terminated by a signal;
    the following number is the signal that terminated the command.

When called without a `command`,
`os.execute` returns a boolean that is true if a shell is available."}}
     :exit {:metadata {:fnl/arglist [:?code :?close] :fnl/docstring
                       "Calls the ISO C function `exit` to terminate the host program.
If `code` is `true`,
the returned status is `EXIT_SUCCESS`;
if `code` is `false`,
the returned status is `EXIT_FAILURE`;
if `code` is a number,
the returned status is this number.
The default value for `code` is `true`.

If the optional second argument `close` is true,
the function closes the Lua state before exiting."}}
     :getenv {:metadata {:fnl/arglist [:varname] :fnl/docstring
                         "Returns the value of the process environment variable `varname`
or `fail` if the variable is not defined."}}
     :remove {:metadata {:fnl/arglist [:filename] :fnl/docstring
                         "Deletes the file (or empty directory, on POSIX systems)
with the given name.
If this function fails, it returns `fail`
plus a string describing the error and the error code.
Otherwise, it returns true."}}
     :rename {:metadata {:fnl/arglist [:oldname :newname] :fnl/docstring
                         "Renames the file or directory named `oldname` to `newname`.
If this function fails, it returns `fail`,
plus a string describing the error and the error code.
Otherwise, it returns true."}}
     :setlocale {:metadata {:fnl/arglist [:locale :?category] :fnl/docstring
                            "Sets the current locale of the program.
`locale` is a system-dependent string specifying a locale;
`category` is an optional string describing which category to change:
`\"all\"`, `\"collate\"`, `\"ctype\"`,
`\"monetary\"`, `\"numeric\"`, or `\"time\"`;
the default category is `\"all\"`.
The function returns the name of the new locale,
or `fail` if the request cannot be honored.

If `locale` is the empty string,
the current locale is set to an implementation-defined native locale.
If `locale` is the string \"`C`\",
the current locale is set to the standard C locale.

When called with `nil` as the first argument,
this function only returns the name of the current locale
for the given category.

This function may be not thread safe
because of its reliance on C function `setlocale`."}}
     :time {:metadata {:fnl/arglist [:?table] :fnl/docstring
                       "Returns the current time when called without arguments,
or a time representing the local date and time specified by the given table.
This table must have fields `year`, `month`, and `day`,
and may have fields
`hour` (default is 12),
`min` (default is 0),
`sec` (default is 0),
and `isdst` (default is `nil`).
Other fields are ignored.
For a description of these fields, see the `os.date` function.

When the function is called,
the values in these fields do not need to be inside their valid ranges.
For instance, if `sec` is -10,
it means 10 seconds before the time specified by the other fields;
if `hour` is 1000,
it means 1000 hours after the time specified by the other fields.

The returned value is a number, whose meaning depends on your system.
In POSIX, Windows, and some other systems,
this number counts the number
of seconds since some given start time (the \"epoch\").
In other systems, the meaning is not specified,
and the number returned by `time` can be used only as an argument to
`os.date` and `os.difftime`.

When called with a table,
`os.time` also normalizes all the fields
documented in the `os.date` function,
so that they represent the same time as before the call
but with values inside their valid ranges."}}
     :tmpname {:metadata {:fnl/arglist [] :fnl/docstring
                          "Returns a string with a file name that can
be used for a temporary file.
The file must be explicitly opened before its use
and explicitly removed when no longer needed.

In POSIX systems,
this function also creates a file with that name,
to avoid security risks.
(Someone else might create the file with wrong permissions
in the time between getting the name and creating the file.)
You still have to open the file to use it
and to remove it (even if you do not use it).

When possible,
you may prefer to use `io.tmpfile`,
which automatically removes the file when the program ends."}}}}
   :package
   {:metadata {:fnl/docstring "The package library provides basic facilities for loading modules in Lua."}
    :fields
    {:config {:metadata {:fnl/docstring
                         "A string describing some compile-time configurations for packages.
This string is a sequence of lines:

* The first line is the directory separator string.
  Default is '`\\`' for Windows and '`/`' for all other systems.

* The second line is the character that separates templates in a path.
  Default is '`;`'.

* The third line is the string that marks the
  substitution points in a template.
  Default is '`?`'.

* The fourth line is a string that, in a path in Windows,
  is replaced by the executable's directory.
  Default is '`!`'.

* The fifth line is a mark to ignore all text after it
  when building the `luaopen_` function name.
  Default is '`-`'."}}
     :cpath {:metadata {:fnl/docstring
                        "A string with the path used by `require`
to search for a C loader.

Lua initializes the C path `package.cpath` in the same way
it initializes the Lua path `package.path`,
using the environment variable `LUA_CPATH_5_4`,
or the environment variable `LUA_CPATH`,
or a default path defined in `luaconf.h`."}}
     :loaded {:metadata {:fnl/docstring
                         "A table used by `require` to control which
modules are already loaded.
When you require a module `modname` and
`(. package.loaded modname)` is not false,
`require` simply returns the value stored there.

This variable is only a reference to the real table;
assignments to this variable do not change the
table used by `require`.
The real table is stored in the C registry,
indexed by the key `LUA_LOADED_TABLE`, a string."}}
     :loadlib {:metadata {:fnl/arglist [:libname :funcname] :fnl/docstring
                          "Dynamically links the host program with the C library `libname`.

If `funcname` is \"`*`\",
then it only links with the library,
making the symbols exported by the library
available to other dynamically linked libraries.
Otherwise,
it looks for a function `funcname` inside the library
and returns this function as a C function.
So, `funcname` must follow the `lua_CFunction` prototype.

This is a low-level function.
It completely bypasses the package and module system.
Unlike `require`,
it does not perform any path searching and
does not automatically adds extensions.
`libname` must be the complete file name of the C library,
including if necessary a path and an extension.
`funcname` must be the exact name exported by the C library
(which may depend on the C compiler and linker used).

This functionality is not supported by ISO C.
As such, it is only available on some platforms
(Windows, Linux, Mac OS X, Solaris, BSD,
plus other Unix systems that support the `dlfcn` standard).

This function is inherently insecure,
as it allows Lua to call any function in any readable dynamic
library in the system.
(Lua calls any function assuming the function
has a proper prototype and respects a proper protocol
(see `lua_CFunction`).
Therefore,
calling an arbitrary function in an arbitrary dynamic library
more often than not results in an access violation.)"}}
     :path {:metadata {:fnl/docstring
                       "A string with the path used by `require`
to search for a Lua loader.

At start-up, Lua initializes this variable with
the value of the environment variable `LUA_PATH_5_4` or
the environment variable `LUA_PATH` or
with a default path defined in `luaconf.h`,
if those environment variables are not defined.
A \"`;;`\" in the value of the environment variable
is replaced by the default path."}}
     :preload {:metadata {:fnl/docstring
                          "A table to store loaders for specific modules
(see `require`).

This variable is only a reference to the real table;
assignments to this variable do not change the
table used by `require`.
The real table is stored in the C registry,
indexed by the key `LUA_PRELOAD_TABLE`, a string."}}
     :searchers {:metadata {:fnl/docstring
                            "A table used by `require` to control how to find modules.

Each entry in this table is a `searcher function`.
When looking for a module,
`require` calls each of these searchers in ascending order,
with the module name (the argument given to `require`) as its
sole argument.
If the searcher finds the module,
it returns another function, the `module loader`,
plus an extra value, a `loader data`,
that will be passed to that loader and
returned as a second result by `require`.
If it cannot find the module,
it returns a string explaining why
(or `nil` if it has nothing to say).

Lua initializes this table with four searcher functions.

The first searcher simply looks for a loader in the
`package.preload` table.

The second searcher looks for a loader as a Lua library,
using the path stored at `package.path`.
The search is done as described in function `package.searchpath`.

The third searcher looks for a loader as a C library,
using the path given by the variable `package.cpath`.
Again,
the search is done as described in function `package.searchpath`.
For instance,
if the C path is the string

```fnl
\"./?.so;./?.dll;/usr/local/?/init.so\"
```

the searcher for module `foo`
will try to open the files `./foo.so`, `./foo.dll`,
and `/usr/local/foo/init.so`, in that order.
Once it finds a C library,
this searcher first uses a dynamic link facility to link the
application with the library.
Then it tries to find a C function inside the library to
be used as the loader.
The name of this C function is the string \"`luaopen_`\"
concatenated with a copy of the module name where each dot
is replaced by an underscore.
Moreover, if the module name has a hyphen,
its suffix after (and including) the first hyphen is removed.
For instance, if the module name is `a.b.c-v2.1`,
the function name will be `luaopen_a_b_c`.

The fourth searcher tries an *all-in-one loader*.
It searches the C path for a library for
the root name of the given module.
For instance, when requiring `a.b.c`,
it will search for a C library for `a`.
If found, it looks into it for an open function for
the submodule;
in our example, that would be `luaopen_a_b_c`.
With this facility, a package can pack several C submodules
into one single library,
with each submodule keeping its original open function.

All searchers except the first one (preload) return as the extra value
the file path where the module was found,
as returned by `package.searchpath`.
The first searcher always returns the string \"`:preload:`\".

Searchers should raise no errors and have no side effects in Lua.
(They may have side effects in C,
for instance by linking the application with a library.)"}}
     :searchpath {:metadata {:fnl/arglist [:name :path :?sep :?rep] :fnl/docstring
                             "Searches for the given `name` in the given `path`.

A path is a string containing a sequence of
*templates* separated by semicolons.
For each template,
the function replaces each interrogation mark (if any)
in the template with a copy of `name`
wherein all occurrences of `sep`
(a dot, by default)
were replaced by `rep`
(the system's directory separator, by default),
and then tries to open the resulting file name.

For instance, if the path is the string

```fnl
\"./?.lua;./?.lc;/usr/local/?/init.lua\"
```

the search for the name `foo.a`
will try to open the files
`./foo/a.lua`, `./foo/a.lc`, and
`/usr/local/foo/a/init.lua`, in that order.

Returns the resulting name of the first file that it can
open in read mode (after closing the file),
or `fail` plus an error message if none succeeds.
(This error message lists all file names it tried to open.)"}}}}
   :pairs {:metadata {:fnl/arglist [:t]
                      :fnl/docstring "If `t` has a metamethod `__pairs`, calls it with `t` as argument and
returns the first three results from the call.

Otherwise, returns three values: the
[`next`](https://lua.org/manual/5.4/manual.html#pdf-next) function, the
table `t`, and **nil**, so that the construction

```fnl
(each [k v (pairs t) <body>)
```

will iterate over all key--value pairs of table `t`.

See function [`next`](https://lua.org/manual/5.4/manual.html#pdf-next) for
the caveats of modifying the table during its traversal."}}
   :pcall {:metadata {:fnl/arglist [:f :...]
                      :fnl/docstring "Calls the function `f` with the given arguments in *protected mode*.
This means that any error inside `f` is not propagated; instead, `pcall`
catches the error and returns a status code. Its first result is the
status code (a boolean), which is **true** if the call succeeds without
errors. In such case, `pcall` also returns all results from the call,
after this first result. In case of any error, `pcall` returns **false**
plus the error object. Note that errors caught by `pcall` do not call a
message handler."}}
   :print {:metadata {:fnl/arglist [:...]
                      :fnl/docstring "Receives any number of arguments and prints their values to `stdout`,
converting each argument to a string following the same rules of
[`tostring`](https://lua.org/manual/5.4/manual.html#pdf-tostring).

The function `print` is not intended for formatted output, but only as
a quick way to show a value, for instance for debugging. For complete
control over the output, use
[`string.format`](https://lua.org/manual/5.4/manual.html#pdf-string.format)
and [`io.write`](https://lua.org/manual/5.4/manual.html#pdf-io.write)."}}
   :rawequal {:metadata {:fnl/arglist [:v1 :v2]
                         :fnl/docstring "Checks whether `v1` is equal to `v2`, without invoking the `__eq`
metamethod. Returns a boolean."}}
   :rawget {:metadata {:fnl/arglist [:table :index]
                       :fnl/docstring "Gets the real value of `(. table index)`, without using the `__index`
metavalue. `table` must be a table; `index` may be any value."}}
   :rawlen {:metadata {:fnl/arglist [:v]
                       :fnl/docstring "Returns the length of the object `v`, which must be a table or a string,
without invoking the `__len` metamethod. Returns an integer."}}
   :rawset {:metadata {:fnl/arglist [:table :index :value]
                       :fnl/docstring "Sets the real value of `(. table index)` to `value`, without using the
`__newindex` metavalue. `table` must be a table, `index` any value
different from **nil** and NaN, and `value` any Lua value.

This function returns `table`."}}
   :require {:metadata {:fnl/arglist [:modname]
                        :fnl/docstring "Loads the given module. The function starts by looking into the
[`package.loaded`](https://lua.org/manual/5.4/manual.html#pdf-package.loaded)
table to determine whether `modname` is already loaded. If it is, then
`require` returns the value stored at `(. package.loaded modname)`. (The
absence of a second result in this case signals that this call did not
have to load the module.) Otherwise, it tries to find a *loader* for the
module.

To find a loader, `require` is guided by the table
[`package.searchers`](https://lua.org/manual/5.4/manual.html#pdf-package.searchers).
Each item in this table is a search function, that searches for the module
in a particular way. By changing this table, we can change how `require`
looks for a module. The following explanation is based on the default
configuration for
[`package.searchers`](https://lua.org/manual/5.4/manual.html#pdf-package.searchers).

First `require` queries `(. package.preload modname)`. If it has a value,
this value (which must be a function) is the loader. Otherwise `require`
searches for a Lua loader using the path stored in
[`package.path`](https://lua.org/manual/5.4/manual.html#pdf-package.path).
If that also fails, it searches for a C loader using the path stored in
[`package.cpath`](https://lua.org/manual/5.4/manual.html#pdf-package.cpath).
If that also fails, it tries an *all-in-one* loader (see
[`package.searchers`](https://lua.org/manual/5.4/manual.html#pdf-package.searchers)).

Once a loader is found, `require` calls the loader with two arguments:
`modname` and an extra value, a *loader data*, also returned by the
searcher. The loader data can be any value useful to the module; for the
default searchers, it indicates where the loader was found. (For
instance, if the loader came from a file, this extra value is the file
path.) If the loader returns any non-nil value, `require` assigns the
returned value to `(. package.loaded modname)`. If the loader does not
return a non-nil value and has not assigned any value to
`(. package.loaded modname)`, then `require` assigns **true** to this
entry. In any case, `require` returns the final value of
`(. package.loaded modname)`. Besides that value, `require` also returns as
a second result the loader data returned by the searcher, which
indicates how `require` found the module.

If there is any error loading or running the module, or if it cannot
find any loader for the module, then `require` raises an error."}}
   :select {:metadata {:fnl/arglist [:index :...]
                       :fnl/docstring "If `index` is a number, returns all arguments after argument number
`index`; a negative number indexes from the end (-1 is the last
argument). Otherwise, `index` must be the string `\"#\"`, and `select`
returns the total number of extra arguments it received."}}
   :setmetatable {:metadata {:fnl/arglist [:table :metatable]
                             :fnl/docstring "Sets the metatable for the given table. If `metatable` is **nil**,
removes the metatable of the given table. If the original metatable has
a `__metatable` field, raises an error.

This function returns `table`.

To change the metatable of other types from Lua code, you must use the
debug library ([§6.10](https://lua.org/manual/5.4/manual.html#6.10))."}}
   :string
   {:metadata {:fnl/docstring "This library provides generic functions for string manipulation, such as finding and extracting substrings, and pattern matching. When indexing a string in Lua, the first character is at position 1 (not at 0, as in C). Indices are allowed to be negative and are interpreted as indexing backwards, from the end of the string. Thus, the last character is at position -1, and so on.

You can use the string functions in object-oriented style. For instance, `(string.byte s i)` can be written as `(s:byte i)`"}
    :fields
    {:byte {:metadata {:fnl/arglist [:s :?i :?j] :fnl/docstring
                       "Returns the internal numeric codes of the characters `(. s i)`,
`(. s (+ i 1))`, ..., `(. s j)`.
The default value for `i` is 1;
the default value for `j` is `i`.
These indices are corrected
following the same rules of function `string.sub`.

Numeric codes are not necessarily portable across platforms."}}
     :char {:metadata {:fnl/arglist [:...] :fnl/docstring
                       "Receives zero or more integers.
Returns a string with length equal to the number of arguments,
in which each character has the internal numeric code equal
to its corresponding argument.

Numeric codes are not necessarily portable across platforms."}}
     :dump {:metadata {:fnl/arglist [:function :?strip] :fnl/docstring
                       "Returns a string containing a binary representation
(a *binary chunk*)
of the given function,
so that a later `load` on this string returns
a copy of the function (but with new upvalues).
If `strip` is a true value,
the binary representation may not include all debug information
about the function,
to save space.

Functions with upvalues have only their number of upvalues saved.
When (re)loaded,
those upvalues receive fresh instances.
(See the `load` function for details about
how these upvalues are initialized.
You can use the debug library to serialize
and reload the upvalues of a function
in a way adequate to your needs.)"}}
     :find {:metadata {:fnl/arglist [:s :pattern :?init :?plain] :fnl/docstring
                       "Looks for the first match of
`pattern` in the string `s`.
If it finds a match, then `find` returns the indices of `s`
where this occurrence starts and ends;
otherwise, it returns `fail`.
A third, optional numeric argument `init` specifies
where to start the search;
its default value is 1 and can be negative.
A `true` as a fourth, optional argument `plain`
turns off the pattern matching facilities,
so the function does a plain \"find substring\" operation,
with no characters in `pattern` being considered magic.

If the pattern has captures,
then in a successful match
the captured values are also returned,
after the two indices."}}
     :format {:metadata {:fnl/arglist [:formatstring :...] :fnl/docstring
                         "Returns a formatted version of its variable number of arguments
following the description given in its first argument,
which must be a string.
The format string follows the same rules as the ISO C function `sprintf`.
The only differences are that the conversion specifiers and modifiers
`F`, `n`, `*`, `h`, `L`, and `l` are not supported
and that there is an extra specifier, `q`.
Both width and precision, when present,
are limited to two digits.

The specifier `q` formats booleans, nil, numbers, and strings
in a way that the result is a valid constant in Lua source code.
Booleans and nil are written in the obvious way
(`true`, `false`, `nil`).
Floats are written in hexadecimal,
to preserve full precision.
A string is written between double quotes,
using escape sequences when necessary to ensure that
it can safely be read back by the Lua interpreter.
For instance, the call

```fnl
(string.format \"%q\", \"a string with \\\"quotes\\\" and \\n new line\")
```

may produce the string:

```fnl
\"a string with \\\\\\\"quotes\\\\\\\" and \\\\n new line\"
```

This specifier does not support modifiers (flags, width, precision).

The conversion specifiers
`A`, `a`, `E`, `e`, `f`,
`G`, and `g` all expect a number as argument.
The specifiers `c`, `d`,
`i`, `o`, `u`, `X`, and `x`
expect an integer.
When Lua is compiled with a C89 compiler,
the specifiers `A` and `a` (hexadecimal floats)
do not support modifiers.

The specifier `s` expects a string;
if its argument is not a string,
it is converted to one following the same rules of `tostring`.
If the specifier has any modifier,
the corresponding string argument should not contain embedded zeros.

The specifier `p` formats the pointer
returned by `lua_topointer`.
That gives a unique string identifier for tables, userdata,
threads, strings, and functions.
For other values (numbers, nil, booleans),
this specifier results in a string representing
the pointer `NULL`."}}
     :gmatch {:metadata {:fnl/arglist [:s :pattern :?init] :fnl/docstring
                         "Returns an iterator function that,
each time it is called,
returns the next captures from `pattern`
over the string `s`.
If `pattern` specifies no captures,
then the whole match is produced in each call.
A third, optional numeric argument `init` specifies
where to start the search;
its default value is 1 and can be negative.

As an example, the following loop
will iterate over all the words from string `s`,
printing one per line:

```fnl
(let [s \"hello world from Lua\"]
  (each [w (string.gmatch s \"%a+\")]
    (print w))
```

The next example collects all pairs `key=value` from the
given string into a table:

```fnl
(let [t {}
      s \"from=world, to=Lua\"]
  (each [k v (string.gmatch s \"(%w+)=(%w+)\")]
    (set (. t k) v))
  t)
```

For this function, a caret '`^`' at the start of a pattern does not
work as an anchor, as this would prevent the iteration."}}
     :gsub {:metadata {:fnl/arglist [:s :pattern :repl :?n] :fnl/docstring
                       "Returns a copy of `s`
in which all (or the first `?n`, if given)
occurrences of the `pattern` have been
replaced by a replacement string specified by `repl`,
which can be a string, a table, or a function.
`gsub` also returns, as its second value,
the total number of matches that occurred.
The name `gsub` comes from *Global SUBstitution*.

If `repl` is a string, then its value is used for replacement.
The character `%` works as an escape character:
any sequence in `repl` of the form `%*d*`,
with *d* between 1 and 9,
stands for the value of the *d*-th captured substring;
the sequence `%0` stands for the whole match;
the sequence `%%` stands for a single `%`.

If `repl` is a table, then the table is queried for every match,
using the first capture as the key.

If `repl` is a function, then this function is called every time a
match occurs, with all captured substrings passed as arguments,
in order.

In any case,
if the pattern specifies no captures,
then it behaves as if the whole pattern was inside a capture.

If the value returned by the table query or by the function call
is a string or a number,
then it is used as the replacement string;
otherwise, if it is `false` or `nil`,
then there is no replacement
(that is, the original match is kept in the string).

Here are some examples:

```fnl
(local x (string.gsub \"hello world\" \"(%w+)\" \"%1 %1\"))
; x=\"hello hello world world\"

(local x (string.gsub \"hello world\" \"%w+\" \"%0 %0\" 1))
; x=\"hello hello world\"

(local x (string.gsub \"hello world from Lua\" \"(%w+)%s*(%w+)\" \"%2 %1\"))
; x=\"world hello Lua from\"

(local x (string.gsub \"home = $HOME, user = $USER\" \"%$(%w+)\" os.getenv))
; x=\"home = /home/roberto, user = roberto\"

(local x (string.gsub \"4+5 = $return 4+5$\" \"%$(.-)%$\" (fn [s] ((load s)))))
; x=\"4+5 = 9\"

(local t {:name \"lua\" :version \"5.4\"})
(local x (string.gsub \"$name-$version.tar.gz\" \"%$(%w+)\" t))
; x=\"lua-5.4.tar.gz\"
```"}}
     :len {:metadata {:fnl/arglist [:s] :fnl/docstring
                      "Receives a string and returns its length.
The empty string `\"\"` has length 0.
Embedded zeros are counted,
so `\"a\\000bc\\000\"` has length 5."}}
     :lower {:metadata {:fnl/arglist [:s] :fnl/docstring
                        "Receives a string and returns a copy of this string with all
uppercase letters changed to lowercase.
All other characters are left unchanged.
The definition of what an uppercase letter is depends on the current locale."}}
     :match {:metadata {:fnl/arglist [:s :pattern :?init] :fnl/docstring
                        "Looks for the first *match* of
the `pattern` in the string `s`.
If it finds one, then `match` returns
the captures from the pattern;
otherwise it returns `fail`.
If `pattern` specifies no captures,
then the whole match is returned.
A third, optional numeric argument `init` specifies
where to start the search;
its default value is 1 and can be negative."}}
     :pack {:metadata {:fnl/arglist [:fmt :v1 :v2 :...] :fnl/docstring
                       "Returns a binary string containing the values `v1`, `v2`, etc.
serialized in binary form (packed)
according to the format string `fmt`."}}
     :packsize {:metadata {:fnl/arglist [:fmt] :fnl/docstring
                           "Returns the length of a string resulting from `string.pack`
with the given format.
The format string cannot have the variable-length options
'`s`' or '`z`'."}}
     :rep {:metadata {:fnl/arglist [:s :n :?sep] :fnl/docstring
                      "Returns a string that is the concatenation of `n` copies of
the string `s` separated by the string `sep`.
The default value for `sep` is the empty string
(that is, no separator).
Returns the empty string if `n` is not positive.

(Note that it is very easy to exhaust the memory of your machine
with a single call to this function.)"}}
     :reverse {:metadata {:fnl/arglist [:s] :fnl/docstring
                          "Returns a string that is the string `s` reversed."}}
     :sub {:metadata {:fnl/arglist [:s :i :?j] :fnl/docstring
                      "Returns the substring of `s` that
starts at `i`  and continues until `j`;
`i` and `j` can be negative.
If `j` is absent, then it is assumed to be equal to -1
(which is the same as the string length).
In particular,
the call `(string.sub s 1 j)` returns a prefix of `s`
with length `j`,
and `(string.sub s (- i))` (for a positive `i`)
returns a suffix of `s`
with length `i`.

If, after the translation of negative indices,
`i` is less than 1,
it is corrected to 1.
If `j` is greater than the string length,
it is corrected to that length.
If, after these corrections,
`i` is greater than `j`,
the function returns the empty string."}}
     :unpack {:metadata {:fnl/arglist [:fmt :s :?pos] :fnl/docstring
                         "Returns the values packed in string `s`
according to the format string `fmt`.
An optional `pos` marks where
to start reading in `s` (default is 1).
After the read values,
this function also returns the index of the first unread byte in `s`."}}
     :upper {:metadata {:fnl/arglist [:s] :fnl/docstring
                        "Receives a string and returns a copy of this string with all
lowercase letters changed to uppercase.
All other characters are left unchanged.
The definition of what a lowercase letter is depends on the current locale."}}}}
   :table
   {:metadata {:fnl/docstring "This library provides generic functions for table manipulation.

Remember that, whenever an operation needs the length of a table, all caveats about the length operator apply. All functions ignore non-numeric keys in the tables given as arguments."}
    :fields
    {:concat {:metadata {:fnl/arglist [:list :?sep :?i :?j] :fnl/docstring
                         "Given a list where all elements are strings or numbers,
returns the string `(.. (. list i) sep (. list (+ i 1)) sep ... sep .. (. list j))`.
The default value for `sep` is the empty string,
the default for `i` is 1,
and the default for `j` is `(length list)`.
If `i` is greater than `j`, returns the empty string."}}
     :insert {:metadata {:fnl/arglist [:list :?pos :value] :fnl/docstring
                         "Inserts element `value` at position `pos` in `list`,
shifting up the elements
`(. list pos), (. list (+ pos 1)), ..., (. list (length list))`.
The default value for `pos` is `(+ (length list) 1)`,
so that a call `(table.insert t x)` inserts `x` at the end
of the list `t`."}}
     :move {:metadata {:fnl/arglist [:a1 :f :e :t :?a2] :fnl/docstring
                       "Moves elements from the table `a1` to the table `a2`,
performing the equivalent to the following
multiple assignment:
`(set ((. a2 t) ...) (values (. a1 f) ... (. a1 e))`.
The default for `a2` is `a1`.
The destination range can overlap with the source range.
The number of elements to be moved must fit in a Lua integer.

Returns the destination table `a2`."}}
     :pack {:metadata {:fnl/arglist [:...] :fnl/docstring
                       "Returns a new table with all arguments stored into keys 1, 2, etc.
and with a field \"`n`\" with the total number of arguments.
Note that the resulting table may not be a sequence,
if some arguments are `nil`."}}
     :remove {:metadata {:fnl/arglist [:list :?pos] :fnl/docstring
                         "Removes from `list` the element at position `pos`,
returning the value of the removed element.
When `pos` is an integer between 1 and `(length list)`,
it shifts down the elements
`(. list (+ pos 1)), (. list (+ pos 2)), ..., (. list (length list))`
and erases element `(. list (length list))`;
The index `pos` can also be 0 when `(length list)` is 0,
or `(length list) + 1`.

The default value for `pos` is `(length list)`,
so that a call `(table.remove l)` removes the last element
of the list `l`."}}
     :sort {:metadata {:fnl/arglist [:list :?comp] :fnl/docstring
                       "Sorts the list elements in a given order, *in-place*,
from `(. list 1)` to `(. list (length list))`.
If `comp` is given,
then it must be a function that receives two list elements
and returns true when the first element must come
before the second in the final order,
so that, after the sort,
`(<= i j)` implies `(not (comp (. list j) (. list i)))`.
If `comp` is not given,
then the standard Lua operator `<` is used instead.

The `comp` function must define a consistent order;
more formally, the function must define a strict weak order.
(A weak order is similar to a total order,
but it can equate different elements for comparison purposes.)

The sort algorithm is not stable:
Different elements considered equal by the given order
may have their relative positions changed by the sort."}}
     :unpack {:metadata {:fnl/arglist [:list :?i :?j] :fnl/docstring
                         "Returns the elements from the given list.
This function is equivalent to

```fnl
(values (. list i) (. list (+ i 1)) ... (. list j))
```

By default, `i` is 1 and `j` is `(length list)`."}}}}
   :tonumber {:metadata {:fnl/arglist [:e :?base]
                         :fnl/docstring "When called with no `base`, `tonumber` tries to convert its argument to
a number. If the argument is already a number or a string convertible to
a number, then `tonumber` returns this number; otherwise, it returns
**fail**.

The conversion of strings can result in integers or floats, according to
the lexical conventions of Lua (see
[§3.1](https://lua.org/manual/5.4/manual.html#3.1)). The string may have
leading and trailing spaces and a sign.

When called with `base`, then `e` must be a string to be interpreted as
an integer numeral in that base. The base may be any integer between 2
and 36, inclusive. In bases above 10, the letter \'`A`\' (in either
upper or lower case) represents 10, \'`B`\' represents 11, and so forth,
with \'`Z`\' representing 35. If the string `e` is not a valid numeral
in the given base, the function returns **fail**."}}
   :tostring {:metadata {:fnl/arglist [:v]
                         :fnl/docstring "Receives a value of any type and converts it to a string in a
human-readable format.

If the metatable of `v` has a `__tostring` field, then `tostring` calls
the corresponding value with `v` as argument, and uses the result of the
call as its result. Otherwise, if the metatable of `v` has a `__name`
field with a string value, `tostring` may use that string in its final
result.

For complete control of how numbers are converted, use
[`string.format`](https://lua.org/manual/5.4/manual.html#pdf-string.format)."}}
   :type {:metadata {:fnl/arglist [:v]
                     :fnl/docstring "Returns the type of its only argument, coded as a string. The possible
results of this function are \"`nil`\" (a string, not the value
**nil**), \"`number`\", \"`string`\", \"`boolean`\", \"`table`\",
\"`function`\", \"`thread`\", and \"`userdata`\"."}}
   :utf8
   {:metadata {:fnl/docstring "This library provides basic support for UTF-8 encoding. It provides all its functions inside the table `utf8`. This library does not provide any support for Unicode other than the handling of the encoding. Any operation that needs the meaning of a character, such as character classification, is outside its scope.

Unless stated otherwise, all functions that expect a byte position as a parameter assume that the given position is either the start of a byte sequence or one plus the length of the subject string. As in the string library, negative indices count from the end of the string.

Functions that create byte sequences accept all values up to `0x7FFFFFFF`, as defined in the original UTF-8 specification; that implies byte sequences of up to six bytes.

Functions that interpret byte sequences only accept valid sequences (well formed and not overlong). By default, they only accept byte sequences that result in valid Unicode code points, rejecting values greater than `10FFFF` and surrogates. A boolean argument `lax`, when available, lifts these checks, so that all values up to `0x7FFFFFFF` are accepted. (Not well formed and overlong sequences are still rejected.)"}
    :fields
    {:char {:metadata {:fnl/arglist [:...] :fnl/docstring
                       "Receives zero or more integers,
converts each one to its corresponding UTF-8 byte sequence
and returns a string with the concatenation of all these sequences."}}
     :charpattern {:metadata {:fnl/docstring
                              "The pattern (a string, not a function) \"`[\0-\x7F\xC2-\xFD][\x80-\xBF]*`\",
which matches exactly one UTF-8 byte sequence,
assuming that the subject is a valid UTF-8 string."}}
     :codes {:metadata {:fnl/arglist [:s :?lax] :fnl/docstring
                        "Returns values so that the construction

```fnl
(each [p c (utf8.codes s)]
  <body>)
```

will iterate over all UTF-8 characters in string `s`,
with `p` being the position (in bytes) and `c` the code point
of each character.
It raises an error if it meets any invalid byte sequence."}}
     :codepoint {:metadata {:fnl/arglist [:s :?i :?j :?lax] :fnl/docstring
                            "Returns the code points (as integers) from all characters in `s`
that start between byte position `i` and `j` (both included).
The default for `i` is 1 and for `j` is `i`.
It raises an error if it meets any invalid byte sequence."}}
     :len {:metadata {:fnl/arglist [:s :?i :?j :?lax] :fnl/docstring
                      "Returns the number of UTF-8 characters in string `s`
that start between positions `i` and `j` (both inclusive).
The default for `i` is 1 and for `j` is -1.
If it finds any invalid byte sequence,
returns `fail` plus the position of the first invalid byte."}}
     :offset {:metadata {:fnl/arglist [:s :n :?i] :fnl/docstring
                         "Returns the position (in bytes) where the encoding of the
`n`-th character of `s`
(counting from position `i`) starts.
A negative `n` gets characters before position `i`.
The default for `i` is 1 when `n` is non-negative
and `#s + 1` otherwise,
so that `utf8.offset(s, -n)` gets the offset of the
`n`-th character from the end of the string.
If the specified character is neither in the subject
nor right after its end,
the function returns `fail`.

As a special case,
when `n` is 0 the function returns the start of the encoding
of the character that contains the `i`-th byte of `s`.

This function assumes that `s` is a valid UTF-8 string."}}}}
   :warn {:metadata {:fnl/arglist [:msg1 :...]
                     :fnl/docstring "Emits a warning with a message composed by the concatenation of all its
arguments (which should be strings).

By convention, a one-piece message starting with \'`@`\' is intended to
be a *control message*, which is a message to the warning system itself.
In particular, the standard warning function in Lua recognizes the
control messages \"`@off`\", to stop the emission of warnings, and
\"`@on`\", to (re)start the emission; it ignores unknown control
messages."}}
   :xpcall {:metadata {:fnl/arglist [:f :msgh :...]
                       :fnl/docstring "This function is similar to [`pcall`](https://lua.org/manual/5.4/manual.html#pdf-pcall), except that it sets a
new message handler `msgh`."}}})

(fn apply-bindings [docs]
  (each [k v (pairs docs)]
    (set v.binding (sym k))
    (if v.fields
      (apply-bindings v.fields))))

(apply-bindings docs)
(set docs._G.fields docs)

docs
