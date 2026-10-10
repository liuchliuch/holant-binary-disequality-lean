import Holant.Certificates.TetrahedralEightPort.OrbitActions
import Holant.Platonic.StabilizerCode.LocalAxisClifford
import Holant.Platonic.StabilizerShortening.CliffordAffine
import Holant.Platonic.StabilizerShortening.AffineTools
import Holant.Platonic.StabilizerLine.LiteralAffine
import Holant.ReedMuller.CharacterFlat.NoInverse
import Holant.Platonic.TetrahedralLocalization.OneStep

/-! Affinity of the source's actual six-port safe cone.  The local actions
are normalized to genuine unitary Pauli-normalizing Cliffords with exact,
nonzero exterior scales.  No finite candidate list is identified with an orbit.
-/
namespace Holant.Certificates.TetrahedralEightPort.SafeAffine
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Certificates.MatchingProductBridge
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess
open Holant.ReedMuller.CharacterFlat
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
open Holant.Platonic.StabilizerErasure Holant.Platonic.StabilizerShortening
open OrbitActions
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem SafeAffine_site_eq_local (p : Fin 6) (M : Matrix2) (f : SixTensor) :
    siteAction p M f = localLinear p M f := by
  ext x
  simp [siteAction,localLinear,Fin.insertNth_removeNth]

def SafeAffineLocalS : Matrix2 := fun a b =>
  if a=b then (if a then Complex.I else 1) else 0

theorem SafeAffine_phase_exact (p : Fin 6) (f : SixTensor) :
    (Program.phase (siteQuadratic p) false).run f = localLinear p SafeAffineLocalS f := by
  funext x
  simp only [Program.run,phaseAction,phaseExponent,siteQuadratic_eval]
  cases hx : x p <;>
    simp [localLinear,SafeAffineLocalS,hx,bitValue,fourthRootPhase,
      ZMod.val_one_eq_one_mod]

theorem SafeAffine_translate_exact (p : Fin 6) (f : SixTensor) :
    (Program.translate (unitWord p)).run f = localLinear p (qubitPauli 1) f := by
  funext x
  simp only [Program.run,translateAction,wordVector_add_unit]
  cases hx : x p <;> simp [localLinear,qubitPauli,hx]

def SafeAffineGeneratorProgram (p : Fin 6) (b : Bool) : Program 6 :=
  if b then .comp (.phase (siteQuadratic p) false)
    (.hadamard 1 5 (siteCoordinates p)) else .translate (unitWord p)

def SafeAffineGeneratorScale (b : Bool) : ℂ :=
  if b then (sqrtTwo : ℂ)*(1+Complex.I) else Complex.I

theorem SafeAffineGeneratorScale_ne_zero (b : Bool) : SafeAffineGeneratorScale b ≠ 0 := by
  cases b
  · exact Complex.I_ne_zero
  · exact mul_ne_zero (by exact_mod_cast sqrtTwo_ne_zero)
      (by intro h; have hh := congrArg Complex.re h; norm_num at hh)

/-- Both source generator matrices are exact nonzero scalar multiples of
actual Clifford operators, in the literal physical port convention. -/
theorem SafeAffine_generator_exact (p : Fin 6) (b : Bool) (f : SixTensor) :
    localLinear p (localGenerator b) f =
      SafeAffineGeneratorScale b • (SafeAffineGeneratorProgram p b).clifford.operator f := by
  cases b
  · rw [localGenerator_false]
    change localLinear p (Matrix.of Q1) f = Complex.I •
      (Program.translate (unitWord p)).run f
    rw [SafeAffine_translate_exact]
    ext x
    cases hx : x p <;> simp [localLinear,Q1,qubitPauli,hx]
  · rw [localGenerator_true]
    simp only [SafeAffineGeneratorScale,SafeAffineGeneratorProgram,ite_true,
      Program.clifford_apply]
    change localLinear p _ f = _ •
      (Program.phase (siteQuadratic p) false).run
        ((Program.hadamard 1 5 (siteCoordinates p)).run f)
    rw [site_hadamard,SafeAffine_site_eq_local]
    rw [SafeAffine_phase_exact,local_mul]
    have hs : (sqrtTwo : ℂ) ≠ 0 := by exact_mod_cast sqrtTwo_ne_zero
    ext x
    cases hx : x p <;>
      simp [localLinear,Matrix.mul_apply,SafeAffineLocalS,localH,Q0,Q1,Q2,Q3,
        Signature.equality,hx] <;>
      field_simp [show (Real.sqrt 2 : ℂ)≠0 from hs] <;>
      ring_nf <;> simp [Complex.I_sq,sub_eq_add_neg]

def SafeAffineWordProgram (p : Fin 6) : List Bool → Program 6
  | [] => .identity
  | b :: w => .comp (SafeAffineGeneratorProgram p b) (SafeAffineWordProgram p w)

def SafeAffineWordScale : List Bool → ℂ
  | [] => 1
  | b :: w => SafeAffineGeneratorScale b * SafeAffineWordScale w

theorem SafeAffineWordScale_ne_zero (w : List Bool) : SafeAffineWordScale w ≠ 0 := by
  induction w with
  | nil => exact one_ne_zero
  | cons b w ih => exact mul_ne_zero (SafeAffineGeneratorScale_ne_zero b) ih

theorem SafeAffine_word_exact (p : Fin 6) (w : List Bool) (f : SixTensor) :
    localLinear p (generatorWord w) f =
      SafeAffineWordScale w • (SafeAffineWordProgram p w).clifford.operator f := by
  induction w generalizing f with
  | nil => simp [generatorWord,SafeAffineWordScale,SafeAffineWordProgram,local_one,
      Program.run]
  | cons b w ih =>
    rw [generatorWord,←local_mul,ih,map_smul,SafeAffine_generator_exact,smul_smul]
    simp only [SafeAffineWordScale,SafeAffineWordProgram,Program.clifford_apply,Program.run]
    rw [mul_comm]

/-- Every actual tetrahedral matrix, including arbitrary nonzero complex
rescaling, is normalized to a genuine Clifford on the selected physical port. -/
theorem SafeAffine_actual_clifford (p : Fin 6) (M : Matrix2)
    (hM : groupDirection .tetrahedral M) :
    ∃ c : ℂ, c≠0 ∧ ∃ C : AnalyticClifford 6,
      ∀ f : SixTensor, localLinear p M f = c • C.operator f := by
  obtain ⟨w,c,hc,rfl⟩ := (tetrahedral_generated M).mp hM
  refine ⟨c*SafeAffineWordScale w,mul_ne_zero hc (SafeAffineWordScale_ne_zero w),
    (SafeAffineWordProgram p w).clifford,?_⟩
  intro f
  rw [local_scale_matrix,SafeAffine_word_exact,smul_smul]

theorem SafeAffine_local (p : Fin 6) (M : Matrix2)
    (hM : groupDirection .tetrahedral M) (f : SixTensor) (hf : ComplexAffine f) :
    ComplexAffine (localLinear p M f) := by
  obtain ⟨c,hc,C,he⟩ := SafeAffine_actual_clifford p M hM
  rw [he]
  exact (analyticClifford_affine C f hf).scale c

theorem SafeAffine_permute (e : Equiv.Perm (Fin 6))
    (f : SixTensor) (hf : ComplexAffine f) : ComplexAffine (portLinear e f) :=
  affine_complex_precompose hf _ (coordinates_isAffineMap e)

def M0 : SixTensor := fun x => Q0 (x 0) (x 1)*Q0 (x 2) (x 3)*Q0 (x 4) (x 5)
def H0 : SixTensor := hCore

theorem M0_ne_zero : M0 ≠ 0 := by
  intro h
  have hh := congrFun h zeroSix
  norm_num [M0,Q0,Signature.equality,zeroSix] at hh

theorem H0_ne_zero : H0 ≠ 0 := by
  intro h
  have hh := congrFun h zeroSix
  change hCore zeroSix=0 at hh
  rw [hCore_zero] at hh
  exact one_ne_zero hh

def SafeAffineMSystem : AffineSystem 6 where
  rows := 3
  matrix := ![![1,1,0,0,0,0],![0,0,1,1,0,0],![0,0,0,0,1,1]]
  rhs := fun _ => 0

theorem SafeAffineMSystem_holds (x : Word 6) :
    SafeAffineMSystem.Holds x ↔ x 0=x 1 ∧ x 2=x 3 ∧ x 4=x 5 := by
  simp only [AffineSystem.Holds,SafeAffineMSystem,Fin.forall_fin_succ,
    Fin.sum_univ_succ]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    cases h3 : x 3 <;> cases h4 : x 4 <;> cases h5 : x 5 <;>
    norm_num [bitValue,h0,h1,h2,h3,h4,h5] <;> decide

theorem M0_affine : ComplexAffine M0 := by
  have he : M0 = complexAffineFormula 1 SafeAffineMSystem (QuadraticPhase.zero 6) := by
    funext x
    simp only [M0,Q0,Signature.equality,complexAffineFormula,SafeAffineMSystem_holds,
      QuadraticPhase.zero_eval,fourthRootPhase_zero,one_mul]
    split_ifs <;> simp_all
  rw [he]
  exact complexAffine_formula _ _ _

def SafeAffineHSystem : AffineSystem 6 where
  rows := 1
  matrix := fun _ _ => 1
  rhs := fun _ => 0

def SafeAffineHPairs : List (Fin 6 × Fin 6) := [(0,3),(1,2),(2,3),(0,4),(1,4)]

def SafeAffineHPhase : QuadraticPhase 6 where
  constant := 0
  linear := ![0,0,2,0,0,0]
  mixed j k := if (j,k) ∈ SafeAffineHPairs then 2 else 0
  even_mixed j k _ := by
    by_cases h : (j,k) ∈ SafeAffineHPairs
    · exact Or.inr (by simp [h])
    · exact Or.inl (by simp [h])

theorem SafeAffineHSystem_holds (x : Word 6) :
    SafeAffineHSystem.Holds x ↔
      bitValue (ZMod 2) (x 0)+bitValue (ZMod 2) (x 1)+
      bitValue (ZMod 2) (x 2)+bitValue (ZMod 2) (x 3)+
      bitValue (ZMod 2) (x 4)+bitValue (ZMod 2) (x 5)=0 := by
  simp [SafeAffineHSystem,AffineSystem.Holds,Fin.sum_univ_succ,add_assoc]

theorem SafeAffineHPhase_eval (x : Word 6) : SafeAffineHPhase.eval x =
    2*bitValue (ZMod 4) (x 2)+2*(
      bitValue (ZMod 4) (x 0)*bitValue (ZMod 4) (x 3)+
      bitValue (ZMod 4) (x 1)*bitValue (ZMod 4) (x 2)+
      bitValue (ZMod 4) (x 2)*bitValue (ZMod 4) (x 3)+
      bitValue (ZMod 4) (x 0)*bitValue (ZMod 4) (x 4)+
      bitValue (ZMod 4) (x 1)*bitValue (ZMod 4) (x 4)) := by
  norm_num [SafeAffineHPhase,SafeAffineHPairs,QuadraticPhase.eval,Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 4000000 in
theorem SafeAffineH_formula :
    H0 = complexAffineFormula 1 SafeAffineHSystem SafeAffineHPhase := by
  have h2 : (2 : ZMod 2)=0 := by decide
  have h3 : (3 : ZMod 2)=1 := by decide
  have h4 : (4 : ZMod 2)=0 := by decide
  have h5 : (5 : ZMod 2)=1 := by decide
  have h6 : (6 : ZMod 2)=0 := by decide
  funext x
  cases x0 : x 0 <;> cases x1 : x 1 <;> cases x2 : x 2 <;>
    cases x3 : x 3 <;> cases x4 : x 4 <;> cases x5 : x 5 <;>
    norm_num [H0,hCore,bellKernel,parityKernel,sign,intSign,bit,boolEquiv,
      complexAffineFormula,SafeAffineHSystem_holds,SafeAffineHPhase_eval,
      bitValue,fourthRootPhase,x0,x1,x2,x3,x4,x5,ZMod.val_natCast,
      ZMod.val_ofNat,ZMod.val_zero,ZMod.natCast_self,Complex.I_sq] <;>
    simp [h2,h3,h4,h5,h6]

theorem H0_affine : ComplexAffine H0 := by
  rw [SafeAffineH_formula]
  exact complexAffine_formula _ _ _

def M0Point : Point := Projectivization.mk ℂ M0 M0_ne_zero
def H0Point : Point := Projectivization.mk ℂ H0 H0_ne_zero

/-- The source matching and H-core sets are genuine orbits of physical
tetrahedral port matrices and permutations, before any finite enumeration. -/
def MatchingOrbit : Set Point := ActualOrbit M0Point
def HCoreOrbit : Set Point := ActualOrbit H0Point
def SafeSet : Set Point := MatchingOrbit ∪ HCoreOrbit

/-- Zero together with every nonzero representative of a source safe
projective point. Arbitrary nonzero complex exterior scales are retained. -/
def SafeCone (f : SixTensor) : Prop :=
  f=0 ∨ ∃ hf : f≠0, Projectivization.mk ℂ f hf ∈ SafeSet

def SafeAffinePoint (q : Point) : Prop :=
  ∃ f : SixTensor, ∃ hf : f≠0,
    Projectivization.mk ℂ f hf=q ∧ ComplexAffine f

theorem SafeAffine_point_representative {q : Point} (hq : SafeAffinePoint q)
    (f : SixTensor) (hf : f≠0) (he : Projectivization.mk ℂ f hf=q) :
    ComplexAffine f := by
  obtain ⟨g,hg,hgq,hga⟩ := hq
  obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ f g hf hg).mp (he.trans hgq.symm)
  rw [←hc]
  exact hga.scale c

theorem SafeAffine_actual_step (a : ActualOperation) (q : Point)
    (hq : SafeAffinePoint q) : SafeAffinePoint (actualStep a q) := by
  obtain ⟨f,hf,rfl,hfa⟩ := hq
  cases a with
  | dress p M hM =>
    refine ⟨localLinear p M f,?_,rfl,SafeAffine_local p M hM f hfa⟩
    intro hz
    exact hf (local_injective p M (groupDirection_det_ne_zero .tetrahedral hM)
      (by simpa using hz))
  | permute e =>
    refine ⟨portLinear e f,?_,rfl,SafeAffine_permute e f hfa⟩
    intro hz
    exact hf (port_injective e (by simpa using hz))

theorem SafeAffine_orbit {base q : Point} (hb : SafeAffinePoint base)
    (hq : q ∈ ActualOrbit base) : SafeAffinePoint q := by
  induction hq with
  | base => exact hb
  | next a h ih => exact SafeAffine_actual_step a _ ih

theorem SafeAffine_safe_point {q : Point} (hq : q∈SafeSet) : SafeAffinePoint q := by
  rcases hq with h|h
  · exact SafeAffine_orbit ⟨M0,M0_ne_zero,rfl,M0_affine⟩ h
  · exact SafeAffine_orbit ⟨H0,H0_ne_zero,rfl,H0_affine⟩ h

/-- Every vector in the source six-port safe cone is literally affine in
the unchanged normalized computational basis. -/
theorem safeCone_affine (f : SixTensor) (hf : SafeCone f) : ComplexAffine f := by
  rcases hf with rfl|⟨hn,hp⟩
  · exact affine_zero_complex
  · exact SafeAffine_point_representative (SafeAffine_safe_point hp) f hn rfl

theorem safeCone_zero : SafeCone 0 := Or.inl rfl

theorem safeCone_M0 : SafeCone M0 :=
  Or.inr ⟨M0_ne_zero,Or.inl Generated.base⟩

theorem safeCone_H0 : SafeCone H0 :=
  Or.inr ⟨H0_ne_zero,Or.inr Generated.base⟩

theorem safeCone_scale (f : SixTensor) (hf : SafeCone f) (c : ℂ) : SafeCone (c • f) := by
  by_cases hc : c=0
  · simp only [hc,zero_smul]
    exact safeCone_zero
  rcases hf with rfl|⟨hn,hp⟩
  · simpa using safeCone_zero
  · have hcn : c • f≠0 := smul_ne_zero hc hn
    refine Or.inr ⟨hcn,?_⟩
    have he : Projectivization.mk ℂ (c • f) hcn=Projectivization.mk ℂ f hn :=
      (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨c,rfl⟩
    rwa [he]

/-- A support consequence of physical shortening at arity eight.  The factor
alternative is an arbitrary proper tensor cut, not the source's stronger 2|6
alternative; this theorem does not claim the full eight-port audit. -/
theorem safeCards_factor_or_affine (g : Signature ℂ 8)
    (hcards : ∀ p : (Bool ⊕ Fin 6) ≃ Fin 8, ∀ K : Kernel ℂ,
      groupDirection .tetrahedral K → SafeCone (pairCard p K g)) :
    Holant.Pauli.ExoticKlein.Fiber.HasProperTensorFactor g ∨ ComplexAffine g := by
  by_cases hg : ComplexAffine g
  · exact Or.inr hg
  rcases Holant.Platonic.TetrahedralLocalization.factor_or_nonaffine_pair g (by decide) hg
    with hfactor|hcard
  · exact Or.inl hfactor
  · obtain ⟨n,p,r,hn,ha⟩ := hcard
    have hdim := Holant.Platonic.TetrahedralLocalization.pair_arity p
    have he : n=6 := by omega
    subst n
    have hk : groupDirection .tetrahedral (TetrahedralAffine.complexKernel r) :=
      ⟨1,one_ne_zero,_,TetrahedralAffine.kernel_base r,by simp⟩
    exact False.elim (ha (safeCone_affine _ (hcards p _ hk)))

/-- Every tensor-prime eight-port tensor with actual safe six-port cards is
affine, obtained without identifying a finite candidate list with an orbit. -/
theorem tensorPrime_safeCards_affine (g : Signature ℂ 8)
    (hprime : ¬Holant.Pauli.ExoticKlein.Fiber.HasProperTensorFactor g)
    (hcards : ∀ p : (Bool ⊕ Fin 6) ≃ Fin 8, ∀ K : Kernel ℂ,
      groupDirection .tetrahedral K → SafeCone (pairCard p K g)) :
    ComplexAffine g :=
  (safeCards_factor_or_affine g hcards).resolve_left hprime

end
end Holant.Certificates.TetrahedralEightPort.SafeAffine
