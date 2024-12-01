build: src/Main.idr
	../Idris2/bootstrap-build/bin/idris2 --inc chez --build idris2-rust.ipkg

hello: hello.idr src/Main.idr
	./build/exec/idris2-rust hello.idr -o hello
