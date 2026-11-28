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
	cd formal/cogentic && "$(LAKE)" build Cogentic.RandomizedEndToEnd Cogentic.RandomizedEpochVacuity Cogentic.RandomizedCostedEpoch Cogentic.RandomizedConcreteEpoch Cogentic.RandomizedConcreteEpochChecks Cogentic.RandomizedConcreteEpochCost Cogentic.RandomizedConcreteStageCost Cogentic.RandomizedConcreteStageCostS1S2 Cogentic.RandomizedConcreteStageCostS3 Cogentic.RandomizedConcreteStageCostS469 Cogentic.RandomizedConcreteStageCostS5 Cogentic.RandomizedConcreteStageCostS8 Cogentic.RandomizedC5Algebra Cogentic.RandomizedC5AlgebraSub Cogentic.RandomizedC5Coupling Cogentic.RandomizedL19Poisson Cogentic.RandomizedL19Energy Cogentic.RandomizedL19EnergyMass Cogentic.RandomizedL19EnergyMassFinite Cogentic.RandomizedL19ZeroMode Cogentic.RandomizedL19ZeroModeFinite Cogentic.RandomizedL19Thin Cogentic.RandomizedL19ThinFinite Cogentic.RandomizedL19Full Cogentic.RandomizedConcreteTV Cogentic.RandomizedL18_4 Cogentic.RandomizedL18_4CellCount Cogentic.RandomizedL18_4CellData Cogentic.RandomizedL18_4Numerator Cogentic.RandomizedL18_4Mass Cogentic.RandomizedL18_4Thin Cogentic.RandomizedL18_4ThinAggregate Cogentic.RandomizedL18_4Full Cogentic.RandomizedL18_4LargeSieve Cogentic.RandomizedL18_4LargeSieveInputs Cogentic.RandomizedL18_4LargeSieveResidual Cogentic.RandomizedL18_4EnergyBudget Cogentic.RandomizedL18_4ConvolutionEnergy Cogentic.RandomizedL18_4LatticeCount Cogentic.RandomizedL19SecondMoment Cogentic.RandomizedL19Muq Cogentic.RandomizedL20_2 Cogentic.RandomizedL20_2Sub Cogentic.RandomizedL20_2Char Cogentic.RandomizedL20_2Saddle Cogentic.RandomizedL20_2SmoothLower Cogentic.RandomizedL20_2SmoothMass Cogentic.RandomizedL20_2PaperMass Cogentic.RandomizedL20_2PaperSmooth Cogentic.RandomizedL20_2ScalarWidth Cogentic.RandomizedL20_2ConcentrationLeaf Cogentic.RandomizedL20_2CoordinateEnergy Cogentic.RandomizedL20_2Decay Cogentic.RandomizedL20_2DecayNonempty Cogentic.RandomizedL20_2Width Cogentic.RandomizedL20_2Fit Cogentic.RandomizedL20_2BandScale Cogentic.RandomizedL20_4 Cogentic.RandomizedL20_4Sub Cogentic.RandomizedL20_4Conditioned Cogentic.RandomizedL20_4Interior Cogentic.RandomizedL20_4TwoPoint Cogentic.RandomizedL20_4EventMass Cogentic.RandomizedL20_4Incoming Cogentic.RandomizedL20_4ChildLower Cogentic.RandomizedL20_4PairAlt Cogentic.RandomizedL20_4LeafAssembly Cogentic.RandomizedL20_4Mean Cogentic.RandomizedL20_4InteriorBase Cogentic.RandomizedL20_4BaseSource Cogentic.RandomizedL20_4EtaSource Cogentic.RandomizedL20_4RationalSource Cogentic.RandomizedL20_4Top Cogentic.RandomizedL20_4Additive Cogentic.RandomizedL21_2 Cogentic.RandomizedL21_2Sub Cogentic.RandomizedL21_2Perron Cogentic.RandomizedL21_2Density Cogentic.RandomizedL21_2LocalCount Cogentic.RandomizedL21_2Shift Cogentic.RandomizedL21_2Fourier Cogentic.RandomizedL21_2Vertical Cogentic.RandomizedL21_2LineBound Cogentic.RandomizedL21_2Remainder Cogentic.RandomizedL21_2PaperLocal Cogentic.RandomizedL21_2Tent Cogentic.RandomizedL21_2Abel Cogentic.RandomizedL27_1 Cogentic.RandomizedL27_1Sub Cogentic.RandomizedL27Analytic Cogentic.RandomizedL27Deuring Cogentic.RandomizedL27Stratification Cogentic.RandomizedL27Hurwitz Cogentic.RandomizedL27Scale Cogentic.RandomizedL27Fiber Cogentic.RandomizedL27Window Cogentic.RandomizedL27TraceClass Cogentic.RandomizedL27Siegel Cogentic.RandomizedL27ClassNumber Cogentic.RandomizedL27Waterhouse Cogentic.RandomizedL27Weighted Cogentic.RandomizedL27StageOne Cogentic.RandomizedL27GcdModel Cogentic.RandomizedL27KillLaw Cogentic.RandomizedL34 Cogentic.RandomizedL34Sub Cogentic.RandomizedL34Analytic Cogentic.RandomizedL34Dedekind Cogentic.RandomizedL34ZeroFree Cogentic.RandomizedL34HalfPlane Cogentic.RandomizedL34BelowOne Cogentic.RandomizedL34DedekindStrip Cogentic.RandomizedL34ClassicalRegion Cogentic.RandomizedL34Stark Cogentic.RandomizedL34ClassicalStark Cogentic.RandomizedL34Range Cogentic.RandomizedL34Sides Cogentic.RandomizedL34ChebotarevSides Cogentic.RandomizedC5Full Cogentic.RandomizedC5GoodIff Cogentic.RandomizedL30 Cogentic.RandomizedL30Sub Cogentic.RandomizedL30Analytic Cogentic.RandomizedL30Younis Cogentic.RandomizedL30Raw Cogentic.RandomizedL30LPP Cogentic.RandomizedL30Global Cogentic.RandomizedL30Relative Cogentic.RandomizedL30Interval Cogentic.RandomizedL30ShortInterval Cogentic.RandomizedL30GlobalLower Cogentic.RandomizedL4 Cogentic.RandomizedL4Sub Cogentic.RandomizedL4Composition Cogentic.RandomizedL4Faithful Cogentic.RandomizedL4SquaringSelection Cogentic.RandomizedL4Cox Cogentic.RandomizedL4Bands Cogentic.RandomizedConcreteFormSpec Cogentic.RandomizedConcreteC3Real Cogentic.RandomizedConcreteC3Budget Cogentic.RandomizedConcreteC3Rough Cogentic.RandomizedDischargedAdapters Cogentic.RandomizedP1 Cogentic.RandomizedP1Sub Cogentic.RandomizedP1Analytic Cogentic.RandomizedP1Prepass Cogentic.RandomizedConcreteHitMass Cogentic.RandomizedConcreteHitMassCount Cogentic.RandomizedC5HalfMass Cogentic.RandomizedPaperL18_4 Cogentic.RandomizedPaperLeafStatements Cogentic.RandomizedPaperEndpoint Cogentic.RandomizedPaperEndpointDischarged Cogentic.RandomizedPaperEndpointFullyDischarged Cogentic.RandomizedPaperEndpointWave13

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
