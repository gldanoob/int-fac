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

.PHONY: check-randomized-lean
check-randomized-lean:
	cd formal/cogentic && "$(LAKE)" build RandomizedFactoring

.PHONY: check-randomized-end-to-end
check-randomized-end-to-end:
	cd formal/cogentic && "$(LAKE)" build Cogentic.RandomizedEndToEnd Cogentic.RandomizedEpochVacuity Cogentic.RandomizedCostedEpoch Cogentic.RandomizedConcreteEpoch Cogentic.RandomizedConcreteEpochChecks Cogentic.RandomizedConcreteEpochCost Cogentic.RandomizedConcreteStageCost Cogentic.RandomizedConcreteStageCostS3 Cogentic.RandomizedConcreteStageCostS8 Cogentic.RandomizedConcreteTV Cogentic.RandomizedL18_4 Cogentic.RandomizedL18_4CellCount Cogentic.RandomizedL18_4Numerator Cogentic.RandomizedL18_4Mass Cogentic.RandomizedL18_4Thin Cogentic.RandomizedL18_4LargeSieve Cogentic.RandomizedL19SecondMoment Cogentic.RandomizedL19Muq Cogentic.RandomizedConcreteHitMass Cogentic.RandomizedConcreteHitMassCount Cogentic.RandomizedPaperL18_4 Cogentic.RandomizedPaperLeafStatements Cogentic.RandomizedPaperEndpoint

.PHONY: check-two-thirds-cached-grh
check-two-thirds-cached-grh:
	cd formal/cogentic && "$(LAKE)" env lean -o .lake/build/lib/lean/CogenticWithGRH.olean CogenticWithGRH.lean

.PHONY: check-two-thirds-short-grh check-randomized-short-grh
check-two-thirds-short-grh: SHORT_GRH_TARGET := CogenticWithGRH
check-randomized-short-grh: SHORT_GRH_TARGET := RandomizedWithGRH
check-two-thirds-short-grh check-randomized-short-grh:
	"$(PYTHON)" formal/short-grh/prepare.py
	cd formal/short-grh && "$(PYTHON)" cache.py "$(LAKE)"
	cd formal/short-grh && "$(LAKE)" build $(SHORT_GRH_TARGET)

check-two-thirds: check-two-thirds-lean
	"$(PYTHON)" -B experiments/cogentic-fixed-window-audit.py
	"$(PYTHON)" -B experiments/cogentic-fixed-rank-audit.py
	"$(PYTHON)" -B experiments/cogentic-two-thirds-extraction-audit.py
	"$(PYTHON)" -B experiments/cogentic-interval-grid-sage.py
	"$(PYTHON)" -B experiments/cogentic-real-extractor-sage.py
