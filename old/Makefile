all:
	agda index.agda

.PHONY: html
html:
	rm -f $(wildcard html/*)
	agda index.agda --html

clean:
	find . -name "*.agdai" -print0 | xargs -0 /bin/rm -f
