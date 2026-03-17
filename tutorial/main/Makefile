BUILD=cabal new-build

LOC=src/Tutorial
SOURCES=$(wildcard $(LOC)/*.hs) $(wildcard $(LOC)/Named/*.hs) $(wildcard $(LOC)/Scoped/*.hs) $(wildcard test/*.hs)
EXTRA=tutorial.cabal cabal.project LICENSE

STUB=$(addprefix ../stub/,$(SOURCES)) $(addprefix ../stub/,$(EXTRA))

STUBREGEX='BEGIN { undef $$/; } s/[\{][-]\s*?SOLN.*?STUBWITH(\s*\r?\n|\s)(.*?)\s*[-][\}]/$$2/sg' 
SOLNREGEX='BEGIN { undef $$/; } s/[\{][-]\s*?SOLN\s*?[-][\}](\s*\r?\n|\s)(.*?)[\{][-]\s*STUBWITH(\s*\r?\n|\s)(.*?)\s*[-][\}]/$$2/sg'

all: stub

clean:
	rm -rf ../stub dist-newstyle/ 

build:
	$(BUILD)

test: Makefile
	echo $(STUB)

stub: Makefile ../stub $(STUB)
	cd ../stub && $(BUILD)


../stub: Makefile $(EXTRA) 
	@echo ====== Creating Stub =========
	@mkdir -p ../stub
	@mkdir -p ../stub/src/
	@mkdir -p ../stub/test/
	@mkdir -p ../stub/src/Tutorial/
	@mkdir -p ../stub/src/Tutorial/Named
	@mkdir -p ../stub/src/Tutorial/Scoped
	cp $(EXTRA) ../stub

../stub/% : % ../stub
	cp $< $@
	@perl -i -pe $(subst SOLN,SOLN,$(STUBREGEX)) $@