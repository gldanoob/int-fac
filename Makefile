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
	cd formal/cogentic && "$(LAKE)" build Cogentic.RandomizedEndToEnd Cogentic.RandomizedEpochVacuity Cogentic.RandomizedCostedEpoch Cogentic.RandomizedConcreteEpoch Cogentic.RandomizedConcreteEpochChecks Cogentic.RandomizedConcreteEpochCost Cogentic.RandomizedConcreteStageCost Cogentic.RandomizedConcreteStageCostS1S2 Cogentic.RandomizedConcreteStageCostS3 Cogentic.RandomizedConcreteStageCostS469 Cogentic.RandomizedConcreteStageCostS5 Cogentic.RandomizedConcreteStageCostS8 Cogentic.RandomizedC5Algebra Cogentic.RandomizedC5AlgebraSub Cogentic.RandomizedC5Coupling Cogentic.RandomizedL19Poisson Cogentic.RandomizedL19Energy Cogentic.RandomizedL19EnergyMass Cogentic.RandomizedL19EnergyMassFinite Cogentic.RandomizedL19ZeroMode Cogentic.RandomizedL19ZeroModeFinite Cogentic.RandomizedL19Thin Cogentic.RandomizedL19ThinFinite Cogentic.RandomizedL19Full Cogentic.RandomizedConcreteTV Cogentic.RandomizedL18_4 Cogentic.RandomizedL18_4CellCount Cogentic.RandomizedL18_4CellData Cogentic.RandomizedL18_4Numerator Cogentic.RandomizedL18_4Mass Cogentic.RandomizedL18_4Thin Cogentic.RandomizedL18_4ThinAggregate Cogentic.RandomizedL18_4Full Cogentic.RandomizedL18_4LargeSieve Cogentic.RandomizedL18_4LargeSieveInputs Cogentic.RandomizedL18_4LargeSieveResidual Cogentic.RandomizedL18_4EnergyBudget Cogentic.RandomizedL18_4LatticeCount Cogentic.RandomizedL19SecondMoment Cogentic.RandomizedL19Muq Cogentic.RandomizedL20_2 Cogentic.RandomizedL20_2Sub Cogentic.RandomizedL20_2Char Cogentic.RandomizedL20_2Saddle Cogentic.RandomizedL20_2SmoothLower Cogentic.RandomizedL20_4 Cogentic.RandomizedL20_4Sub Cogentic.RandomizedL20_4Conditioned Cogentic.RandomizedL21_2 Cogentic.RandomizedL21_2Sub Cogentic.RandomizedL21_2Perron Cogentic.RandomizedL27_1 Cogentic.RandomizedL27_1Sub Cogentic.RandomizedL27Analytic Cogentic.RandomizedL27Deuring Cogentic.RandomizedL34 Cogentic.RandomizedL34Sub Cogentic.RandomizedL34Analytic Cogentic.RandomizedL34Dedekind Cogentic.RandomizedC5Full Cogentic.RandomizedC5GoodIff Cogentic.RandomizedL30 Cogentic.RandomizedL30Sub Cogentic.RandomizedL30Analytic Cogentic.RandomizedL30Younis Cogentic.RandomizedL4 Cogentic.RandomizedL4Sub Cogentic.RandomizedL4Composition Cogentic.RandomizedL4Faithful Cogentic.RandomizedConcreteFormSpec Cogentic.RandomizedConcreteC3Real Cogentic.RandomizedConcreteC3Budget Cogentic.RandomizedConcreteC3Rough Cogentic.RandomizedDischargedAdapters Cogentic.RandomizedP1 Cogentic.RandomizedP1Sub Cogentic.RandomizedP1Analytic Cogentic.RandomizedConcreteHitMass Cogentic.RandomizedConcreteHitMassCount Cogentic.RandomizedC5HalfMass Cogentic.RandomizedPaperL18_4 Cogentic.RandomizedPaperLeafStatements Cogentic.RandomizedPaperEndpoint Cogentic.RandomizedPaperEndpointDischarged Cogentic.RandomizedPaperEndpointFullyDischarged

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
