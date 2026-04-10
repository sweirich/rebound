# Build the tutorial website from Markdown source files.
# Requires: pandoc >= 3.0  (https://pandoc.org/)
#
# Usage:
#   make          – build all HTML lecture pages
#   make haddock  – build and copy Haddock API docs to haddock/
#   make clean    – remove generated HTML and haddock/
#   make watch    – rebuild on changes (requires entr)
#   make serve    – serve locally on http://localhost:8000 (requires python3)

PANDOC   := pandoc
TEMPLATE := template.html
CSS      := style.css
LECTURES := ../lectures

PANDOC_FLAGS := \
  --template=$(TEMPLATE) \
  --highlight-style=pygments \
  --from=markdown+smart \
  --to=html5 \
  -s

HADDOCK_DEST := haddock

.PHONY: all clean watch serve haddock

all: lecture1.html lecture2.html lecture3.html lecture4.html

lecture1.html: $(LECTURES)/Lecture1.md $(TEMPLATE) $(CSS)
	$(PANDOC) $(PANDOC_FLAGS) \
	  --metadata title="Lecture 1: Well-Scoped De Bruijn Representations" \
	  --metadata lecture1-active=true \
	  -o $@ $<

lecture2.html: $(LECTURES)/Lecture2.md $(TEMPLATE) $(CSS)
	$(PANDOC) $(PANDOC_FLAGS) \
	  --metadata title="Lecture 2: Pattern binding" \
	  --metadata lecture2-active=true \
	  -o $@ $<

lecture3.html: $(LECTURES)/Lecture3.md $(TEMPLATE) $(CSS)
	$(PANDOC) $(PANDOC_FLAGS) \
	  --metadata title="Lecture 3: PBT with well-scoped and well-typed terms" \
	  --metadata lecture3-active=true \
	  -o $@ $<

lecture4.html: $(LECTURES)/Lecture4.md $(TEMPLATE) $(CSS)
	$(PANDOC) $(PANDOC_FLAGS) \
	  --metadata title="Lecture 4: CPS — A Scope-Preserving Translation" \
	  --metadata lecture4-active=true \
	  -o $@ $<

haddock:
	cd .. && cabal haddock
	rm -rf $(HADDOCK_DEST)
	cp -r $$(find ../dist-newstyle -path '*/rebound-tutorial-*/doc/html/rebound-tutorial' -type d | head -1) $(HADDOCK_DEST)

clean:
	rm -f lecture1.html lecture2.html lecture3.html lecture4.html
	rm -rf $(HADDOCK_DEST)

watch:
	ls $(LECTURES)/*.md $(TEMPLATE) $(CSS) | entr $(MAKE)

serve: all
	python3 -m http.server 8000 --directory .
