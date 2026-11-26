LEAN ?= $(or $(wildcard $(HOME)/.elan/toolchains/leanprover--lean4---stable/bin/lean),lean)
GP ?= gp
PYTHON ?= python3
LAKE ?= lake

.PHONY: check
check: check-two-thirds-lean
	"$(LEAN)" formal/TapeCover.lean
	"$(LEAN)" formal/CubeSampler.lean
	"$(LEAN)" formal/RawClique.lean
	"$(LEAN)" formal/PrimitiveCertificate.lean
	"$(LEAN)" formal/Secant.lean
	"$(LEAN)" formal/ThreeSquareShell.lean
	"$(LEAN)" formal/CenteredFloor.lean
	@printf '%s\n' 'iferr(read("experiments/check.gp"), err, print(err); quit(1))' | "$(GP)" -fq

.PHONY: check-two-thirds-lean check-two-thirds
check-two-thirds-lean:
	cd formal/cogentic && "$(LAKE)" build

check-two-thirds: check-two-thirds-lean
	"$(PYTHON)" -B experiments/cogentic-fixed-window-audit.py
	"$(PYTHON)" -B experiments/cogentic-fixed-rank-audit.py
	"$(PYTHON)" -B experiments/cogentic-two-thirds-extraction-audit.py
	"$(PYTHON)" -B experiments/cogentic-interval-grid-sage.py
	"$(PYTHON)" -B experiments/cogentic-real-extractor-sage.py

.PHONY: check-one-third
check-one-third:
	"$(PYTHON)" -B experiments/cogentic-parity-compression.py
	"$(PYTHON)" -B experiments/cogentic-threshold-tests.py
	"$(PYTHON)" -B experiments/cogentic-scalar-divisor-count.py
	"$(PYTHON)" -B experiments/cogentic-scalar-progression-sieve.py
	"$(PYTHON)" -B experiments/cogentic-intercept-sampling.py
	"$(PYTHON)" -B experiments/cogentic-stratified-coefficients.py
	"$(PYTHON)" -B experiments/cogentic-coefficient-selection.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-selected-polynomial-split.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-selected-polynomial-recenter.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-pair.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-pair.py --squares
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-pair.py --units
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-index.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-real-gaps.py
	"$(PYTHON)" -B experiments/cogentic-monic-local-laws.py
	"$(PYTHON)" -B experiments/cogentic-intermediate-count.py
	"$(PYTHON)" -B experiments/cogentic-planted-norm-two.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-large-primes.py
	"$(PYTHON)" -B experiments/cogentic-monic-productive-signs.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-scheduled-split.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-kernel-driver.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-blind-grid.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-local-roots.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-ramified-two.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-square-probes.py
	"$(PYTHON)" -B experiments/cogentic-planted-unit-signatures.py
	"$(PYTHON)" -B experiments/cogentic-private-grid-density.py
