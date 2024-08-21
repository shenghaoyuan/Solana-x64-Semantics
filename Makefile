
.open:

.PHONY: open


DEFAULT_FILE = $(CURDIR)/theory/x64DecodeProof.thy

open:
	isabelle jedit -d . $(DEFAULT_FILE)

