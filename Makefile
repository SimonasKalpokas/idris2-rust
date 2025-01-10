# Idris 2 executable
export IDRIS2 ?= idris2

build: src/Main.idr
	IDRIS2 --inc chez --build idris2-rust.ipkg
