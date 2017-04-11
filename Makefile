all: index.html

PANDOC=pandoc \
	--from=markdown \
	-t revealjs \
	--smart \
	--standalone \
  --slide-level=2
#	--section-divs

index.html: totality.md css/custom.css
	$(PANDOC) -o index.html totality.md

publish: index.html
	git commit -am"Commit before publish" || true
	git branch -D gh-pages || true
	git push origin :gh-pages || true
	git checkout --orphan gh-pages
	git rm -rf *.md .gitignore .gitmodules src/
	git add index.html
	mkdir reveal-static || true
	mv reveal.js/css reveal.js/lib reveal.js/js reveal.js/plugin reveal-static/
	rm -rf reveal.js
	mv reveal-static reveal.js
	git add reveal.js
	rm -rf reveal-static src/
	git commit -am"Publish new site"
	git push -u origin gh-pages
	git checkout master && git submodule update

clean:
	rm -f *.ibc
