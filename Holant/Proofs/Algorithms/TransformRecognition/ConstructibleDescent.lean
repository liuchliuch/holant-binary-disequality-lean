import Holant.Tractable.Scalars
import Mathlib.RingTheory.Nullstellensatz


namespace Holant.LocalDrafts.MainChain.TransformRecognition.ConstructibleDescent
open MvPolynomial
noncomputable section
variable {K E σ : Type*} [Field K] [IsAlgClosed K] [Field E] [Algebra K E] [Finite σ]

theorem point_of_proper (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) :
    ∃ y : σ → K, ∀ p ∈ I, aeval y p=0 := by
  obtain ⟨M,hM,hIM⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨y,hy⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hM
  refine ⟨y,?_⟩
  intro p hp
  have hm := hIM hp
  rw [hy] at hm
  exact (MvPolynomial.mem_vanishingIdeal_singleton_iff y p).mp hm

theorem equations_descend {ι : Type*} (p : ι → MvPolynomial σ K)
    (x : σ → E) (hx : ∀ i, aeval x (p i)=0) :
    ∃ y : σ → K, ∀ i, aeval y (p i)=0 := by
  let I := Ideal.span (Set.range p)
  have hker : I ≤ RingHom.ker (aeval x).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hx i
  have hp : I ≠ ⊤ := by
    intro he
    have hone : (1 : MvPolynomial σ K) ∈ I := by rw [he]; trivial
    have h := hker hone
    change aeval x 1=0 at h
    simpa using h
  obtain ⟨y,hy⟩ := point_of_proper I hp
  exact ⟨y,fun i => hy (p i) (Ideal.subset_span ⟨i,rfl⟩)⟩

variable {m k : ℕ}

def augmented (p : Fin m → MvPolynomial σ K) (q : Fin k → MvPolynomial σ K) :
    Fin (m+1) → MvPolynomial (Option σ) K :=
  Fin.snoc (fun i => rename some (p i))
    (X none * ∏ i, rename some (q i) - 1)

def extend (x : σ → E) (t : E) : Option σ → E
  | none => t
  | some j => x j

theorem eval_rename (p : MvPolynomial σ K) (x : Option σ → E) :
    aeval x (rename some p)=aeval (fun j => x (some j)) p := by
  simp [aeval_def,eval₂_rename,Function.comp_def]

theorem augmented_of_constraints (p : Fin m → MvPolynomial σ K)
    (q : Fin k → MvPolynomial σ K) (x : σ → E)
    (hp : ∀ i, aeval x (p i)=0) (hq : ∀ i, aeval x (q i) ≠ 0) :
    ∀ i, aeval (extend x (∏ j, aeval x (q j))⁻¹) (augmented p q i)=0 := by
  have hn : (∏ j, aeval x (q j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hq j)
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [augmented,eval_rename,extend,hn]
  · simp [augmented,eval_rename,extend,hp]

theorem constraints_of_augmented (p : Fin m → MvPolynomial σ K)
    (q : Fin k → MvPolynomial σ K) (x : Option σ → E)
    (hx : ∀ i, aeval x (augmented p q i)=0) :
    (∀ i, aeval (fun j => x (some j)) (p i)=0) ∧
      ∀ i, aeval (fun j => x (some j)) (q i) ≠ 0 := by
  constructor
  · intro i
    simpa [augmented,eval_rename] using hx i.castSucc
  · have hl := hx (Fin.last m)
    have he : x none * (∏ j, aeval (fun v => x (some v)) (q j))=1 := by
      apply sub_eq_zero.mp
      simpa [augmented,eval_rename] using hl
    have hprod : (∏ j, aeval (fun v => x (some v)) (q j)) ≠ 0 := by
      intro hz
      simp [hz] at he
    intro i
    exact Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)

/-- The coefficient field can be AlgebraicComplex and E can be C. Free
normal-form parameters and entries of the shared matrix descend together. -/
theorem constraints_descend (p : Fin m → MvPolynomial σ K)
    (q : Fin k → MvPolynomial σ K) (x : σ → E)
    (hp : ∀ i, aeval x (p i)=0) (hq : ∀ i, aeval x (q i) ≠ 0) :
    ∃ y : σ → K, (∀ i, aeval y (p i)=0) ∧ ∀ i, aeval y (q i) ≠ 0 := by
  obtain ⟨y,hy⟩ := equations_descend (augmented p q)
    (extend x (∏ j, aeval x (q j))⁻¹) (augmented_of_constraints p q x hp hq)
  exact ⟨fun j => y (some j),constraints_of_augmented p q y hy⟩

/-- Ideal membership is the remaining algorithmic question. This equivalence
does not provide a decidable instance by classical proposition choice. -/
theorem constraints_iff_proper (p : Fin m → MvPolynomial σ K)
    (q : Fin k → MvPolynomial σ K) :
    (∃ y : σ → K, (∀ i, aeval y (p i)=0) ∧ ∀ i, aeval y (q i) ≠ 0) ↔
      Ideal.span (Set.range (augmented p q)) ≠ ⊤ := by
  constructor
  · rintro ⟨y,hp,hq⟩ he
    let z := extend y (∏ j, aeval y (q j))⁻¹
    have hz := augmented_of_constraints p q y hp hq
    have hker : Ideal.span (Set.range (augmented p q)) ≤ RingHom.ker (aeval z).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hz i
    have hone : (1 : MvPolynomial (Option σ) K) ∈ Ideal.span (Set.range (augmented p q)) := by
      rw [he]
      trivial
    have h := hker hone
    change aeval z 1=0 at h
    simpa using h
  · intro hp
    obtain ⟨z,hz⟩ := point_of_proper (Ideal.span (Set.range (augmented p q))) hp
    exact ⟨fun j => z (some j),constraints_of_augmented p q z
      (fun i => hz _ (Ideal.subset_span ⟨i,rfl⟩))⟩

/-- Reindex actual finite typed constraints, including dependent tensor
coordinates and a branch's support subtype. No enumeration-completeness
certificate is supplied by the caller. -/
theorem constraints_descend_indexed {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → MvPolynomial σ K) (q : κ → MvPolynomial σ K)
    (x : σ → E) (hp : ∀ i, aeval x (p i)=0) (hq : ∀ i, aeval x (q i) ≠ 0) :
    ∃ y : σ → K, (∀ i, aeval y (p i)=0) ∧ ∀ i, aeval y (q i) ≠ 0 := by
  let ep := Fintype.equivFin ι
  let eq := Fintype.equivFin κ
  obtain ⟨y,hy,hyn⟩ := constraints_descend (fun i => p (ep.symm i))
    (fun i => q (eq.symm i)) x (fun i => hp _) (fun i => hq _)
  exact ⟨y,fun i => by simpa using hy (ep i),fun i => by simpa using hyn (eq i)⟩

def indexedAugmented {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → MvPolynomial σ K) (q : κ → MvPolynomial σ K) :
    Fin (Fintype.card ι+1) → MvPolynomial (Option σ) K :=
  augmented (fun i => p ((Fintype.equivFin ι).symm i))
    (fun i => q ((Fintype.equivFin κ).symm i))

theorem constraints_iff_proper_indexed {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → MvPolynomial σ K) (q : κ → MvPolynomial σ K) :
    (∃ y : σ → K, (∀ i, aeval y (p i)=0) ∧ ∀ i, aeval y (q i) ≠ 0) ↔
      Ideal.span (Set.range (indexedAugmented p q)) ≠ ⊤ := by
  let ep := Fintype.equivFin ι
  let eq := Fintype.equivFin κ
  constructor
  · rintro ⟨y,hy,hyn⟩
    exact (constraints_iff_proper (fun i => p (ep.symm i)) (fun i => q (eq.symm i))).mp
      ⟨y,fun i => hy _,fun i => hyn _⟩
  · intro h
    obtain ⟨y,hy,hyn⟩ :=
      (constraints_iff_proper (fun i => p (ep.symm i)) (fun i => q (eq.symm i))).mpr h
    exact ⟨y,fun i => by simpa using hy (ep i),fun i => by simpa using hyn (eq i)⟩

end
end Holant.LocalDrafts.MainChain.TransformRecognition.ConstructibleDescent
