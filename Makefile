all:
	agda index.agda

lib:
	agda HoTT.agda

.PHONY: html
html:
	rm -f $(wildcard html/*)
	agda index.agda --html

clean:
	find . -name "*.agdai" -print0 | xargs -0 /bin/rm -f
