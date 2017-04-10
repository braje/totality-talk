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
	git rm -f *.md .gitignore
	git add index.html
	git add reveal.js
	git commit -am"Publish new site"
	git push -u origin gh-pages
	git checkout master

clean:
	rm -f *.ibc
