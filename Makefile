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
	"$(PYTHON)" -B experiments/cogentic-short-field-list.py
	"$(PYTHON)" -B experiments/cogentic-weighted-smooth-count.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-all-ideal-reference.py
	@printf '%s\n' 'iferr(read("experiments/cogentic-monic-singular-ideals.gp"), err, print(err); quit(1))' | "$(GP)" -fq
	@printf '%s\n' 'iferr(read("experiments/cogentic-parametric-square-split.gp"), err, print(err); quit(1))' | "$(GP)" -fq
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-degree-certificate-check.py
	"$(PYTHON)" -B experiments/cogentic-growing-pell-pair.py
	"$(PYTHON)" -B experiments/cogentic-partial-sign-lattice.py
	"$(PYTHON)" -B experiments/cogentic-planted-sparse-signs.py
	"$(PYTHON)" -B experiments/cogentic-composite-private-parity.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-exact-grid.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-dyadic-ascent.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-mixed-certificate-check.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-fresh-validation.py --verify experiments/cogentic-monic-fresh-results.jsonl
	"$(PYTHON)" -B experiments/cogentic-monic-fresh-cohort.py --validate experiments/cogentic-monic-fresh-results.jsonl
	"$(PYTHON)" -B experiments/cogentic-monic-mixed-complete.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-quadratic-square-kernel.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-centered-quadratic-density.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-quadratic-supported-kernel.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-monic-216-benchmark.py --verify experiments/cogentic-monic-216-results.jsonl
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-sheared-local-squares.py --verify experiments/cogentic-sheared-results.jsonl
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-sheared-scaling.py --verify experiments/cogentic-sheared-scaling-results.jsonl
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-sheared-qs-witnesses.py --verify experiments/cogentic-sheared-qs-witness-results.jsonl
	"$(PYTHON)" -B experiments/cogentic-rational-root-matching.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-sheared-integer-lifts.py --verify experiments/cogentic-sheared-integer-lift-results.jsonl
	"$(PYTHON)" -B experiments/cogentic-compatible-quadratic-charts.py
	"$(PYTHON)" -B experiments/cogentic-gaussian-smooth-seed-charts.py
	"$(PYTHON)" -B experiments/cogentic-unit-collision-search.py
	"$(PYTHON)" -B experiments/cogentic-deep-unequal-unit-chart.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-unit-collision-verify.py
	GP="$(GP)" "$(PYTHON)" -B experiments/cogentic-cubic-newton-parity.py
	"$(PYTHON)" -B experiments/cogentic-cubic-order-kernel.py
	"$(PYTHON)" -B experiments/cogentic-order-ideal-parity.py
	"$(PYTHON)" -B experiments/cogentic-order-square-kernel.py
	"$(PYTHON)" -B experiments/cogentic-local-square-restriction.py
	"$(PYTHON)" -B experiments/cogentic-radix-grid-density.py
	"$(PYTHON)" -B experiments/cogentic-near-cube-density.py
	"$(PYTHON)" -B experiments/cogentic-mixed-lifted-rank.py
	"$(PYTHON)" -B experiments/cogentic-jacobi-exponent-prefilter.py
	"$(PYTHON)" -B experiments/cogentic-pooled-order-certificates.py
	"$(PYTHON)" -B experiments/cogentic-boxed-order-relations.py
	"$(PYTHON)" -B experiments/cogentic-sparse-support-partition.py
	"$(PYTHON)" -B experiments/cogentic-cofactor-dispersion.py
	"$(PYTHON)" -B experiments/cogentic-ladder-residues.py
	"$(PYTHON)" -B experiments/cogentic-unramified-mark-graph.py
	"$(PYTHON)" -B experiments/cogentic-elliptic-square-cycle.py
	"$(PYTHON)" -B experiments/cogentic-elliptic-cycle-split.py
	"$(PYTHON)" -B experiments/cogentic-elliptic-batch-search.py
	"$(PYTHON)" -B experiments/cogentic-elliptic-local-halves.py
	"$(PYTHON)" -B experiments/cogentic-elliptic-local-saturation.py
	"$(PYTHON)" -B experiments/cogentic-cm-jacobi-triples.py
	"$(PYTHON)" -B experiments/cogentic-varying-norm-torus.py
	"$(PYTHON)" -B experiments/cogentic-varying-norm-torus.py --replay-stage-two
	"$(PYTHON)" -B experiments/cogentic-cm-linear-forms.py
	"$(PYTHON)" -B experiments/cogentic-moving-elliptic-separation.py
	"$(PYTHON)" -B experiments/cogentic-moving-elliptic-separation.py --replay-stage-two
	"$(PYTHON)" -B experiments/cogentic-moving-elliptic-conic.py
	"$(PYTHON)" -B experiments/cogentic-planted-square-masks.py
	@for script in cogentic-cubic-square-resolvent cogentic-bounded-degree-multiples cogentic-prescribed-unit-marks cogentic-common-cofactors-sparse-steps cogentic-rational-gaussian-seed-family cogentic-unit-corrected-family cogentic-joint-gaussian-orders; do \
		printf 'iferr(read("experiments/%s.gp"), err, print(err); quit(1))\n' "$$script" | "$(GP)" -fq || exit 1; \
	done
	@cd experiments && for script in cogentic-cubic-different-kernel cogentic-maximal-ideal-roots cogentic-half-ideal-relations; do \
		printf 'iferr(read("%s.gp"), err, print(err); quit(1))\n' "$$script" | "$(GP)" -fq || exit 1; \
	done
