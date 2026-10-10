import Holant.Platonic.StabilizerCode.CommutingAlignmentRotation

/-! Constructive simultaneous Clifford alignment. A genuine Pauli quarter
turn removes a nonzero shift direction. Induction on the dimension of the
actual shift span then aligns an arbitrary commuting family to Z type. -/
namespace Holant.Platonic.StabilizerCode
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.CharacterFlat
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerErasure
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {ι : Type*}

def alignmentCompose (C D : AnalyticClifford n) : AnalyticClifford n where
  operator := D.operator.trans C.operator
  unitary f g := (C.unitary _ _).trans (D.unitary f g)
  pauli_forward := by
    intro P
    obtain ⟨Q,hQ⟩ := D.pauli_forward P
    obtain ⟨R,hR⟩ := C.pauli_forward Q
    exact ⟨R,fun f => by simp [hQ,hR]⟩
  pauli_inverse := by
    intro P
    obtain ⟨Q,hQ⟩ := C.pauli_inverse P
    obtain ⟨R,hR⟩ := D.pauli_inverse Q
    exact ⟨R,fun f => by simp [hQ,hR]⟩

def shiftSpan (P : ι → Pauli n) : BinaryCode n :=
  Submodule.span (ZMod 2) (Set.range (fun i => (P i).shift))

theorem shift_mem_shiftSpan (P : ι → Pauli n) (i : ι) :
    (P i).shift∈shiftSpan P := Submodule.subset_span ⟨i,rfl⟩

theorem exists_shift_functional (a : BinaryVector n) (ha : a≠0) :
    ∃ell : BinaryVector n →ₗ[ZMod 2] ZMod 2,ell a=1 := by
  have hj : ∃j,a j≠0 := by
    by_contra h
    apply ha
    ext j
    simpa using not_exists.mp h j
  obtain ⟨j,hj⟩ := hj
  exact ⟨LinearMap.proj j,(binary_cases (a j)).resolve_left hj⟩

theorem quarterTurn_eliminates_shift
    (P : ι → Pauli n)
    (hcomm : ∀i j f,(P i).run ((P j).run f)=(P j).run ((P i).run f))
    (p : ι) (alpha : BinaryVector n →ₗ[ZMod 2] ZMod 2)
    (ha : alpha (P p).shift=1) :
    ∃C : AnalyticClifford n,∃Q : ι → Pauli n,
      (∀i f,C.operator ((P i).run f)=(Q i).run (C.operator f)) ∧
      (∀i j f,(Q i).run ((Q j).run f)=(Q j).run ((Q i).run f)) ∧
      Module.finrank (ZMod 2) (shiftSpan Q)<Module.finrank (ZMod 2) (shiftSpan P) := by
  let R := hermitianPauli (P p).shift ((P p).character+alpha)
  let C := quarterTurnClifford R (hermitianPauli_square _ _)
  let Q : ι → Pauli n := fun i => quarterTurnPauli R (P i) false
  have hinter (i : ι) (f : Signature ℂ n) :
      C.operator ((P i).run f)=(Q i).run (C.operator f) :=
    quarterTurn_intertwines R (P i) (hermitianPauli_square _ _) false f
  have hp (i : ι) : pauliPairing R (P i)=alpha (P i).shift := by
    have hh := (pauli_commute_iff (P p) (P i)).mp (hcomm p i)
    simp only [pauliPairing] at hh
    change (P p).character (P i).shift+alpha (P i).shift+
      (P i).character (P p).shift=alpha (P i).shift
    linear_combination hh
  have hs (i : ι) :
      (Q i).shift=(P i).shift+alpha (P i).shift • (P p).shift := by
    change (quarterTurnPauli R (P i) false).shift=_
    rw [quarterTurnPauli_shift,hp]
    rfl
  refine ⟨C,Q,hinter,?_,?_⟩
  · intro i j f
    obtain ⟨g,rfl⟩ := C.operator.surjective f
    rw [←hinter,←hinter,←hinter,←hinter,hcomm]
  · have hle : shiftSpan Q≤shiftSpan P⊓LinearMap.ker alpha := by
      apply Submodule.span_le.mpr
      rintro x ⟨i,rfl⟩
      change (Q i).shift∈shiftSpan P⊓LinearMap.ker alpha
      rw [hs]
      constructor
      · exact (shiftSpan P).add_mem (shift_mem_shiftSpan P i)
          ((shiftSpan P).smul_mem _ (shift_mem_shiftSpan P p))
      · simp [LinearMap.mem_ker,ha,CharTwo.add_self_eq_zero]
    have hlt : shiftSpan P⊓LinearMap.ker alpha<shiftSpan P := by
      apply lt_of_le_of_ne inf_le_left
      intro he
      have hm : (P p).shift∈shiftSpan P⊓LinearMap.ker alpha :=
        he.symm ▸ shift_mem_shiftSpan P p
      have hz : alpha (P p).shift=0 := hm.2
      rw [ha] at hz
      exact one_ne_zero hz
    exact lt_of_le_of_lt (Submodule.finrank_mono hle)
      (Submodule.finrank_lt_finrank_of_lt hlt)

/-- There is no finite-tableau or symplectic-reduction premise: the Clifford
is constructed by descending the finite-dimensional span of the X labels. -/
theorem exists_zero_shift_clifford (P : ι → Pauli n)
    (hcomm : ∀i j f,(P i).run ((P j).run f)=(P j).run ((P i).run f)) :
    ∃C : AnalyticClifford n,∃Q : ι → Pauli n,
      (∀i f,C.operator ((P i).run f)=(Q i).run (C.operator f)) ∧
      ∀i,(Q i).shift=0 := by
  generalize hd : Module.finrank (ZMod 2) (shiftSpan P)=d
  induction d using Nat.strong_induction_on generalizing P with
  | h d ih =>
    by_cases hz : ∀i,(P i).shift=0
    · exact ⟨Program.identity.clifford,P,fun _ _ => rfl,hz⟩
    · obtain ⟨p,hp⟩ := not_forall.mp hz
      obtain ⟨alpha,ha⟩ := exists_shift_functional (P p).shift hp
      obtain ⟨C,Q,hCQ,hQQ,hlt⟩ := quarterTurn_eliminates_shift P hcomm p alpha ha
      obtain ⟨D,R,hDR,hR⟩ := ih (Module.finrank (ZMod 2) (shiftSpan Q))
        (by simpa [hd] using hlt) Q hQQ rfl
      refine ⟨alignmentCompose D C,R,?_,hR⟩
      intro i f
      change D.operator (C.operator ((P i).run f))=(R i).run (D.operator (C.operator f))
      rw [hCQ,hDR]

theorem aligned_involution (C : AnalyticClifford n) (P Q : Pauli n)
    (he : ∀f,C.operator (P.run f)=Q.run (C.operator f))
    (hP : ∀f,P.run (P.run f)=f) (f : Signature ℂ n) : Q.run (Q.run f)=f := by
  obtain ⟨g,rfl⟩ := C.operator.surjective f
  rw [←he,←he,hP]

theorem zero_shift_involution_sign (Q : Pauli n) (hs : Q.shift=0)
    (hQ : ∀f,Q.run (Q.run f)=f) : ∃s : ZMod 2,phaseRoot Q.phase=sign s := by
  have hh := congrFun (hQ (fun _ => 1)) (origin n)
  simp [Pauli.run,hs] at hh
  rcases fourth_cases Q.phase with h|h|h|h
  · exact ⟨0,by simp [h]⟩
  · norm_num [h,phaseRoot] at hh
  · exact ⟨1,by simp [h,phaseRoot]⟩
  · norm_num [h,phaseRoot] at hh

theorem aligned_nonscalar_label (C : AnalyticClifford n) (P Q : Pauli n)
    (he : ∀f,C.operator (P.run f)=Q.run (C.operator f)) (hs : Q.shift=0)
    (hP : ¬IsScalar P.run) : characterLabel Q.character≠0 := by
  intro hz
  have hc : Q.character=0 := by
    apply LinearMap.ext
    intro x
    have hh := characterLabel_dot Q.character x
    simpa [hz,Holant.ReedMuller.LowArity.dot] using hh.symm
  obtain ⟨c,hc⟩ := (pauli_scalar_iff Q).mpr ⟨hs,hc⟩
  apply hP
  refine ⟨c,?_⟩
  intro f
  apply C.operator.injective
  rw [he,hc,map_smul]

/-- Exact simultaneous Z-type alignment, including all signs and preservation
of every nonscalar label. In particular this applies to a finite commuting
family of Hermitian Pauli operators. -/
theorem exists_commuting_pauli_alignment (P : ι → Pauli n)
    (hcomm : ∀i j f,(P i).run ((P j).run f)=(P j).run ((P i).run f))
    (hinv : ∀i f,(P i).run ((P i).run f)=f) :
    ∃C : AnalyticClifford n,∃s : ι → ZMod 2,∃b : ι → BinaryVector n,
      (∀i f,C.operator ((P i).run f)=
        sign (s i) • standardPauli 0 0 (b i) (C.operator f)) ∧
      ∀i,¬IsScalar (P i).run → b i≠0 := by
  obtain ⟨C,Q,hCQ,hQ⟩ := exists_zero_shift_clifford P hcomm
  choose s hs using fun i => zero_shift_involution_sign (Q i) (hQ i)
    (aligned_involution C (P i) (Q i) (hCQ i) (hinv i))
  refine ⟨C,s,fun i => characterLabel (Q i).character,?_,?_⟩
  · intro i f
    rw [hCQ]
    ext x
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [standardPauli_dot]
    simp [Pauli.run,hQ i,hs i,characterLabel_dot,mul_assoc]
  · intro i hi
    exact aligned_nonscalar_label C (P i) (Q i) (hCQ i) (hQ i) hi

theorem exists_commuting_nontrivial_pauli_alignment (P : ι → Pauli n)
    (hcomm : ∀i j f,(P i).run ((P j).run f)=(P j).run ((P i).run f))
    (hinv : ∀i f,(P i).run ((P i).run f)=f)
    (hlabel : ∀i,(P i).shift≠0 ∨ (P i).character≠0) :
    ∃C : AnalyticClifford n,∃s : ι → ZMod 2,∃b : ι → BinaryVector n,
      (∀i f,C.operator ((P i).run f)=
        sign (s i) • standardPauli 0 0 (b i) (C.operator f)) ∧
      ∀i,b i≠0 := by
  obtain ⟨C,s,b,he,hb⟩ := exists_commuting_pauli_alignment P hcomm hinv
  refine ⟨C,s,b,he,?_⟩
  intro i
  apply hb i
  intro hh
  obtain ⟨ha,hc⟩ := (pauli_scalar_iff (P i)).mp hh
  exact (hlabel i).elim (fun h => h ha) (fun h => h hc)

end
end Holant.Platonic.StabilizerCode
