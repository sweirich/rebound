# Find the name of the suite of files we are benchmarking
SUITE_NAME =$(shell grep "impls = [^ ]*" lib/Suite.hs | cut -d" " -f 3)
MACHINE = $(shell uname -n)

OUT = results/$(MACHINE)/$(SUITE_NAME)/time/
OUT_MEM = results/$(MACHINE)/$(SUITE_NAME)/memory/


LC:	lib/*.hs lib/*/*.lhs bench/*.lhs
	stack build

normalize: LC
	rm -rf $(OUT)
	mkdir -p $(OUT)
	uname -a > $(OUT)output.txt
	stack run -- --output $(OUT)eval_bench.html --match prefix "eval/" --json $(OUT)eval_bench.json  >> $(OUT)output.txt
	stack run -- --output $(OUT)nf_bench.html --match prefix "nf/" --json $(OUT)nf_bench.json  >> $(OUT)output.txt
	stack run -- --output $(OUT)random15_bench.html --match prefix "random15/" --json $(OUT)random15_bench.json  >> $(OUT)output.txt

normalize_mem: LC
	rm -rf $(OUT_MEM)
	mkdir -p $(OUT_MEM)
	uname -a > $(OUT_MEM)output.txt
	stack run --profile -- --output $(OUT_MEM)eval_bench.html --match prefix "eval/" --json $(OUT_MEM)eval_bench.json --regress allocated:iters +RTS -T -RTS  >> $(OUT_MEM)output.txt
	stack run --profile -- --output $(OUT_MEM)nf_bench.html --match prefix "nf/" --json $(OUT_MEM)nf_bench.json --regress allocated:iters +RTS -T -RTS  >> $(OUT_MEM)output.txt
	stack run --profile -- --output $(OUT_MEM)random15_bench.html --match prefix "random15/" --json $(OUT_MEM)random15_bench.json --regress allocated:iters +RTS -T -RTS  >> $(OUT_MEM)output.txt