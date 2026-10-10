import Holant.Proofs.Hardness.ComplexSelfdualData
import Holant.Proofs.Hardness.ThreeModeCountingSource
import Holant.Proofs.Hardness.ComplexDynamicCountingSource
import Holant.Proofs.Hardness.NuComplexDynamicCountingSource
import Holant.Proofs.Hardness.EqualModulusThreeModeCountingSource

/-! Closed complex cone counting source. Spectral comparisons and every
branch premise are derived internally from the original coefficients and
the strict norm cone. All four branches keep the same original-field codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexConeHardnessSource
open Computability Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace D
export ComplexSelfdualData (Applicable)
end D
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field presentation targetEncoding targetValue)
end O
namespace Standard
export Holant.LocalDrafts.MainChain.CBStandardNativeHardness.Standard
  (Model injectedEncoding standard_to_witness)
end Standard
set_option backward.isDefEq.respectTransparency false

theorem norm_product (a b : ℂ) : ‖b-a‖*‖a+b‖=‖a^2-b^2‖ := by
  rw [←norm_mul,show (b-a)*(a+b)=-(a^2-b^2) by ring,norm_neg]

variable (M : Signature ℂ 4) (halg : ∀x,IsAlgebraic ℚ (M x)) (h : D.Applicable M)
variable (hcone : ComplexConeEntry.Cone (entries M).b (entries M).d (entries M).c)

include hcone in
theorem cone_product :
    ‖(entries M).d-(entries M).b‖*‖(entries M).b+(entries M).d‖<‖(entries M).c‖^2 := by
  rw [norm_product]
  exact hcone

include h in
theorem threeModeApplicable
    (hsmall : ‖(entries M).b+(entries M).d‖<‖(entries M).c‖ ∧
      ‖(entries M).d-(entries M).b‖<‖(entries M).c‖) : ThreeModeOriginalData.Applicable M :=
  ⟨h.eo,h.oppositeA,h.oppositeB,h.oppositeC,h.nonzeroA,h.nonzeroB,h.nonzeroC,
    hsmall.1,hsmall.2⟩

include h hcone in
theorem muApplicable
    (hmu : ‖(entries M).c‖<‖(entries M).b+(entries M).d‖) :
    ComplexDynamicOriginalData.Applicable M := by
  have hc : 0<‖(entries M).c‖ := norm_pos_iff.mpr h.nonzeroC
  have hsum : 0<‖(entries M).b+(entries M).d‖ := hc.trans hmu
  refine ⟨h.eo,h.oppositeA,h.oppositeB,h.oppositeC,h.nonzeroA,h.nonzeroB,h.nonzeroC,
    norm_pos_iff.mp hsum,?_,?_⟩
  · rw [norm_div]
    exact (div_lt_one hsum).mpr hmu
  · apply (div_lt_one (sq_pos_of_pos hc)).mpr
    rw [norm_mul]
    exact cone_product M hcone

include h hcone in
theorem nuApplicable
    (hnu : ‖(entries M).c‖<‖(entries M).d-(entries M).b‖) :
    NuComplexDynamicOriginalData.Applicable M := by
  have hc : 0<‖(entries M).c‖ := norm_pos_iff.mpr h.nonzeroC
  have hdifference : 0<‖(entries M).d-(entries M).b‖ := hc.trans hnu
  refine ⟨h.eo,h.oppositeA,h.oppositeB,h.oppositeC,h.nonzeroA,h.nonzeroB,h.nonzeroC,
    norm_pos_iff.mp hdifference,?_,?_⟩
  · rw [norm_div]
    exact (div_lt_one hdifference).mpr hnu
  · apply (div_lt_one (sq_pos_of_pos hc)).mpr
    rw [norm_mul,mul_comm]
    exact cone_product M hcone

include h hcone in
theorem equalApplicable
    (hsmall : ¬(‖(entries M).b+(entries M).d‖<‖(entries M).c‖ ∧
      ‖(entries M).d-(entries M).b‖<‖(entries M).c‖))
    (hmu : ¬‖(entries M).c‖<‖(entries M).b+(entries M).d‖)
    (hnu : ¬‖(entries M).c‖<‖(entries M).d-(entries M).b‖) :
    EqualModulusThreeModeOriginalData.Applicable M := by
  have hc : 0<‖(entries M).c‖ := norm_pos_iff.mpr h.nonzeroC
  have hp := cone_product M hcone
  refine ⟨h.eo,h.oppositeA,h.oppositeB,h.oppositeC,h.nonzeroA,h.nonzeroB,h.nonzeroC,?_⟩
  change (‖(entries M).b+(entries M).d‖=‖(entries M).c‖ ∧
      ‖(entries M).d-(entries M).b‖<‖(entries M).c‖) ∨
    (‖(entries M).d-(entries M).b‖=‖(entries M).c‖ ∧
      ‖(entries M).b+(entries M).d‖<‖(entries M).c‖)
  by_cases he : ‖(entries M).b+(entries M).d‖=‖(entries M).c‖
  · rw [he,pow_two] at hp
    exact Or.inl ⟨he,by nlinarith⟩
  · have hplt : ‖(entries M).b+(entries M).d‖<‖(entries M).c‖ :=
      lt_of_le_of_ne (le_of_not_gt hmu) he
    have hneq : ‖(entries M).d-(entries M).b‖=‖(entries M).c‖ := by
      apply le_antisymm (le_of_not_gt hnu)
      exact le_of_not_gt (fun hlt=>hsmall ⟨hplt,hlt⟩)
    exact Or.inr ⟨hneq,hplt⟩

local instance fieldAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'
variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}

/-- Internal exhaustive spectral dispatch in the actual coefficient field. -/
def source (w : SharpPWitness ea f) :
    LengthControlledOracleReduction ea encodingNatBool O.targetEncoding (O.presentation M halg).encoding
      f (O.targetValue M halg) := by
  classical
  by_cases hsmall : ‖(entries M).b+(entries M).d‖<‖(entries M).c‖ ∧
      ‖(entries M).d-(entries M).b‖<‖(entries M).c‖
  · exact ThreeModeCountingSource.source M halg (threeModeApplicable M h hsmall) w
  by_cases hmu : ‖(entries M).c‖<‖(entries M).b+(entries M).d‖
  · exact ComplexDynamicCountingSource.source M halg (muApplicable M h hcone hmu) w
  by_cases hnu : ‖(entries M).c‖<‖(entries M).d-(entries M).b‖
  · exact NuComplexDynamicCountingSource.source M halg (nuApplicable M h hcone hnu) w
  exact EqualModulusThreeModeCountingSource.source M halg
    (equalApplicable M h hcone hsmall hmu hnu) w

include h hcone in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    O.targetEncoding (O.presentation M halg).encoding (O.targetValue M halg) := by
  intro α ea f w
  exact ⟨(source M halg h hcone w).reduction⟩

attribute [local irreducible] source

def outputs (w : SharpPWitness ea f) (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding (O.presentation M halg).encoding (O.targetValue M halg) oracle)
    (x : α) : (source M halg h hcone w).reduction.machine.OutputsInTime oracle (ea.encode x)
      (encodingNatBool.encode (f x)) ((source M halg h hcone w).reduction.time.eval (ea.encode x).length) :=
  (source M halg h hcone w).reduction.correct oracle ho x

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : Standard.Model Δ Q) (input : Bool→Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

/-- Only the source machine's input-only time bound is supplied. -/
def standardSource : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation M halg).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (O.targetValue M halg) :=
  source M halg h hcone (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

attribute [local irreducible] standardSource

def standard_outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding (O.presentation M halg).encoding (O.targetValue M halg) oracle)
    (x : α) :
    (standardSource (ea:=ea) M halg h hcone m input hinj clock htime).reduction.machine.OutputsInTime
      oracle (ea.encode x)
      (encodingNatBool.encode (m.physicalCount (Standard.injectedEncoding ea input hinj) x))
      ((standardSource (ea:=ea) M halg h hcone m input hinj clock htime).reduction.time.eval (ea.encode x).length) :=
  (standardSource (ea:=ea) M halg h hcone m input hinj clock htime).reduction.correct oracle ho x

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexConeHardnessSource
