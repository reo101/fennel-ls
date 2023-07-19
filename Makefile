LUA ?= lua
FENNEL=$(LUA) fennel
EXE=fennel-ls

SRC=$(wildcard src/*.fnl)
SRC+=$(wildcard src/fennel-ls/*.fnl)
SRC+=$(wildcard src/fennel-ls/doc/*.fnl)

DESTDIR ?=
PREFIX ?= /usr/local
BINDIR ?= $(PREFIX)/bin

.PHONY: clean test install ci

all: $(EXE)

$(EXE): $(SRC)
	echo "#!/usr/bin/env $(LUA)" > $@
	LUA_PATH="./src/?.lua" \
		FENNEL_PATH="./src/?.fnl" \
		$(FENNEL) --require-as-include --compile src/fennel-ls.fnl >> $@
	chmod 755 $@

clean:
	rm -f $(EXE)

test:
	TESTING=1 LUA_PATH="./src/?.lua;./?.lua" FENNEL_PATH="./src/?.fnl;./?.fnl" \
		$(FENNEL) test/init.fnl

testall:
	$(MAKE) test LUA=lua5.1
	$(MAKE) test LUA=lua5.2
	$(MAKE) test LUA=lua5.3
	$(MAKE) test LUA=lua5.4
	$(MAKE) test LUA=luajit

install: $(EXE)
	mkdir -p $(DESTDIR)$(BINDIR) && cp $< $(DESTDIR)$(BINDIR)/

ci: testall $(EXE)
