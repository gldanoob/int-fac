LEAN ?= $(or $(wildcard $(HOME)/.elan/toolchains/leanprover--lean4---stable/bin/lean),lean)
GP ?= gp

.PHONY: check
check:
	"$(LEAN)" formal/TapeCover.lean
	"$(LEAN)" formal/RawClique.lean
	@printf '%s\n' 'iferr(read("experiments/check.gp"), err, print(err); quit(1))' | "$(GP)" -fq
