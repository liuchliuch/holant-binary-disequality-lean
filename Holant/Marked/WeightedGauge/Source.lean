import Holant.Marked.WeightedGauge.Batches
import Holant.Marked.WeightedGauge.Factorization
import Holant.Marked.WeightedGauge.PolarizedRanks
import Holant.Marked.WeightedGauge.Sector

/-! Full explicit interface for manuscript Lemma 6.32. Its conclusions are
proved finite-network identities and invariants, rather than a supplied batch
coherence predicate. Gauges and basis changes remain analytic operations. -/
noncomputable section
namespace Holant.Marked.WeightedGauge
open Holant.Tractable
open Holant.Dihedral.PolarizedDeterminant (Cube card phaseMonomial sliceWords insert)
open scoped BigOperators

abbrev sourceWeights {m n : ℕ} (P : Parameters m) (S : Finset (Fin n)) : Fin n → Scalar :=
  setWeights (SupportAtlas.delta P) S

def deltaUnit {m : ℕ} (P : Parameters m) : Scalarˣ :=
  Units.mk0 (SupportAtlas.delta P) (SupportAtlas.delta_ne_zero P)

/-- All four source batch forms and all invariants, stated on literal data. -/
structure SourceFacts {m : ℕ} (P : Parameters m) : Prop where
  range : 4 ≤ m ∧ Even m
  physical_cards : ∀ (F : SignatureFamily Scalar) (q : Signature Scalar 4)
    (reps : SupportAtlas.Representatives F m P.basis) (e : Equiv.Perm (Fin 4)) (p : Bool)
    (t : SupportAtlas.Phase m),
    transport P.basis (SupportAtlas.physicalCard q e (reps.matrix p t)) =
      scale (P.edgeMultiplier*reps.multiplier p t)
        (SupportAtlas.contract0 (SupportAtlas.reorder (P.basis.symm.action q) e)
          (effectiveKernel (SupportAtlas.delta P) p t.val))
  endpoint_push : ∀ M g : Kernel Scalar,
    pairing (Kernel.mul (diagonal (SupportAtlas.delta P)) M) g =
      pairing M (fun a b => bitWeight (SupportAtlas.delta P) a * g a b) ∧
    pairing (Kernel.mul M (diagonal (SupportAtlas.delta P))) g =
      pairing M (fun a b => bitWeight (SupportAtlas.delta P) b * g a b)
  incidence_push : ∀ (out : ℕ) (s : NetworkShape out) (orientation : Fin s.edges → Bool)
    (f : (v : Fin s.vertices) → Signature Scalar (s.arity v)) (E : Fin s.edges → Kernel Scalar),
    (Network.mk s f (fun e => weightedEdge (SupportAtlas.delta P) (orientation e) (E e))).denote =
      (Network.mk s (pushedVertex s orientation (SupportAtlas.delta P) f) E).denote
  fixed_joint_parent : ∀ (out : ℕ) (s : NetworkShape out) (orientation : Fin s.edges → Bool)
    (f : (v : Fin s.vertices) → Signature Scalar (s.arity v)),
    jointParent s (pushedVertex s orientation (SupportAtlas.delta P) f) =
      gauge (portScale s orientation (SupportAtlas.delta P)) (jointParent s f)
  support : ∀ (n : ℕ) (S : Finset (Fin n)) (f : Signature Scalar n) (x : Fin n → Bool),
    gauge (sourceWeights P S) f x = 0 ↔ f x = 0
  incomplete : ∀ (n : ℕ) (S : Finset (Fin n)) (f : Signature Scalar n) (mask : Set (Fin n → Bool)),
    (∃ x ∈ mask, gauge (sourceWeights P S) f x = 0) ↔ (∃ x ∈ mask, f x = 0)
  all_ranks : ∀ (n a b : ℕ) (e : Fin a ⊕ Fin b ≃ Fin n) (S : Finset (Fin n)) (f : Signature Scalar n),
    (flatten e (gauge (sourceWeights P S) f)).rank = (flatten e f).rank
  factorization : ∀ (n : ℕ) (S : Finset (Fin n)) (D : TensorDecomposition Scalar n),
    (gaugedDecomposition (sourceWeights P S) D).value = gauge (sourceWeights P S) D.value
  factorization_pullback : ∀ (n : ℕ) (S : Finset (Fin n)) (D : TensorDecomposition Scalar n)
    (f : Signature Scalar n), D.value = gauge (sourceWeights P S) f →
      (gaugedDecomposition (fun i => (sourceWeights P S i)⁻¹) D).value = f
  factor_lines : ∀ (n : ℕ) (S : Finset (Fin n)) (f g : Signature Scalar n) (c : Scalar),
    gauge (sourceWeights P S) f = c • gauge (sourceWeights P S) g ↔ f = c • g
  phase_substitutions : ∀ t : Scalar,
    effectiveKernel (SupportAtlas.delta P) false t = standardKernel false (SupportAtlas.delta P*t) ∧
    effectiveKernel (SupportAtlas.delta P) true t = SupportAtlas.delta P • standardKernel true (t/SupportAtlas.delta P)
  traces : ∀ (p reverse inverse : Bool) (u v : Scalar), u ≠ 0 → v ≠ 0 →
    ∃ k theta : Scalar, k*theta ≠ 0 ∧ ∀ t : Scalar,
      pairing (if reverse then Kernel.transpose (effectiveKernel (SupportAtlas.delta P) p (phase inverse t))
        else effectiveKernel (SupportAtlas.delta P) p (phase inverse t)) (factor p u v) =
      k * (1+theta*phase inverse t)
  one_term : ∀ (A B t : Scalar) (inverse : Bool), t ≠ 0 →
    ((A ≠ 0 ∧ B=0) ∨ (A=0 ∧ B ≠ 0)) → A+B*phase inverse t ≠ 0
  protected_minor : ∀ (t c0 c1 k0 k1 : Scalarˣ) (a0 a1 b0 b1 r0 r1 s0 s1 : ℤ)
    (M : Matrix Bool Bool Scalar),
    minor (fun i j =>
      (↑(if i then monomial (deltaUnit P) t c1 a1 b1 else monomial (deltaUnit P) t c0 a0 b0) : Scalar) * M i j *
      (↑(if j then monomial (deltaUnit P) t k1 r1 s1 else monomial (deltaUnit P) t k0 r0 s0) : Scalar)) false true false true =
      (↑(monomial (deltaUnit P) t (c0*c1*k0*k1) (a0+a1+r0+r1) (b0+b1+s0+s1)) : Scalar) *
        minor M false true false true
  reversal : ∀ (t : ℂ), t^m=1 →
    let d : ℂ := SupportAtlas.delta P
    (d^2/t)^m=1 ∧ t/d ≠ 0 ∧
      Kernel.transpose (effectiveKernel d true t) = (t/d) • effectiveKernel d true (d^2/t)
  ratios : ∀ (M : Kernel ℂ), M ≠ 0 → SupportAtlas.SafeWeighted m (SupportAtlas.delta P : ℂ) M →
    ∃ p : Bool, (∀ a b, (a ^^ b) ≠ p → M a b=0) ∧
      M false p ≠ 0 ∧ M true (!p) ≠ 0 ∧ ratioCoset m (SupportAtlas.delta P : ℂ) (M true (!p)/M false p)
  inverse_coset : ∀ r : ℂ, ratioCoset m (SupportAtlas.delta P : ℂ) r →
    ratioCoset m (SupportAtlas.delta P : ℂ) r⁻¹
  disjoint_coset : ∀ r : ℂ, r^m=1 → ¬ratioCoset m (SupportAtlas.delta P : ℂ) r
  four_samples : ∀ (out : ℕ) (t0 t1 : Scalar) (h : Signature Scalar (out+2))
    (order : Equiv.Perm (Fin (out+2))) (choice : Bool × Bool),
    pairBatch (SupportAtlas.delta P) h order choice.1 (if choice.2 then t1 else t0) =
      (parentNetwork (pairRouting out order)
        (gauge (sourceWeights P (parentSet (pairRouting out order) (fun _ => false))) h)
        (fun _ => standardKernel choice.1 (if choice.2 then t1 else t0))).denote
  trace_cover : ∀ (N out edges : ℕ) (routing : Fin N ≃ (Fin out ⊕ (Fin edges × Bool)))
    (orientation : Fin edges → Bool) (h : Signature Scalar N) (initial : Fin edges)
    (K0 K1 : Kernel Scalar) (rest : Fin edges → Kernel Scalar) (choice : Bool),
    (parentNetwork routing h (fun e => weightedEdge (SupportAtlas.delta P) (orientation e)
      (traceCoverEdges initial K0 K1 rest choice e))).denote =
      (parentNetwork routing (gauge (sourceWeights P (parentSet routing orientation)) h)
        (traceCoverEdges initial K0 K1 rest choice)).denote
  six_to_four : ∀ (h : Signature Scalar 6) (order : Equiv.Perm (Fin 6)) (p : Bool) (t : Scalar),
    pairBatch (SupportAtlas.delta P) h order p t =
      (parentNetwork (pairRouting 4 order)
        (gauge (sourceWeights P (parentSet (pairRouting 4 order) (fun _ => false))) h)
        (fun _ => standardKernel p t)).denote
  polarization_fixed_parent : ∀ (s : ℕ) (parity : Fin s → Bool) (w : Cube s → ℂ)
    (i k : Fin s), i ≠ k → ∀ (lam : Fin s → ℂ) (a b xi : Bool),
    Polarization.physicalGrid (SupportAtlas.delta P : ℂ) parity w i k lam a b xi =
      ∑ z ∈ sliceWords i k, phaseMonomial lam z *
        Polarization.leftGauge (SupportAtlas.delta P : ℂ) parity i k w (insert i k a xi z) * w (insert i k b xi z)
  polarization_standard : ∀ (s : ℕ) (parity : Fin s → Bool) (w : Cube s → ℂ)
    (i k : Fin s) (lam : Fin s → ℂ) (a b xi : Bool),
    Polarization.physicalGrid (SupportAtlas.delta P : ℂ) parity w i k lam a b xi =
      (bitWeight (SupportAtlas.delta P : ℂ) xi * Polarization.constant (SupportAtlas.delta P : ℂ) parity i k) *
        card w i k (Polarization.shiftedPhases (SupportAtlas.delta P : ℂ) parity i k lam) a b xi
  polarization_nonzero : ∀ (s : ℕ) (parity : Fin s → Bool) (i k : Fin s) (xi : Bool),
    bitWeight (SupportAtlas.delta P : ℂ) xi * Polarization.constant (SupportAtlas.delta P : ℂ) parity i k ≠ 0
  polarization_ranks : ∀ (s : ℕ) (parity : Fin s → Bool) (w : Cube s → ℂ) (i k : Fin s),
    (∀ lam : Fin s → ℂ, (∀ j, lam j^m=1) →
      Holant.Dihedral.PolarizedDeterminant.ThreeRanks
        (Polarization.physicalGrid (SupportAtlas.delta P : ℂ) parity w i k lam)) ↔
    (∀ lam : Fin s → ℂ, (∀ j, lam j^m=1) →
      Holant.Dihedral.PolarizedDeterminant.ThreeRanks (card w i k lam))
  full_grid : ∀ (s : ℕ) (parity : Fin s → Bool) (i k : Fin s) (lam : Fin s → ℂ),
    (∀ j, lam j^m=1) → ∃ mu : Fin s → ℂ, (∀ j, mu j^m=1) ∧
      Polarization.shiftedPhases (SupportAtlas.delta P : ℂ) parity i k mu = lam

/-- **Manuscript Lemma 6.32**, with A's exact source parameters and all four
comparison batches derived from literal incidence or physical matching sums. -/
theorem source_weighted_gauge_transport {m : ℕ} (P : Parameters m) (hP : isA P) : SourceFacts P := by
  have hd := SupportAtlas.delta_ne_zero P
  have hdC : (SupportAtlas.delta P : ℂ) ≠ 0 := by exact_mod_cast hd
  have hrC : (((SupportAtlas.delta P : ℂ)^2)^m)=1 := by exact_mod_cast SupportAtlas.delta_root P
  have hnotC : (SupportAtlas.delta P : ℂ)^m ≠ 1 := by exact_mod_cast source_delta_not_root P hP
  refine {
    range := source_even_range P hP
    physical_cards := fun F q reps e p t => source_physical_card F P hP q reps e p t
    endpoint_push := fun M g => ⟨push_first _ M g, push_second _ M g⟩
    incidence_push := fun _ s orientation f E => network_push s orientation _ f E
    fixed_joint_parent := fun _ s orientation f => jointParent_push s orientation _ f
    support := fun _ S f x => gauge_zero_iff _ (setWeights_ne_zero hd S) f x
    incomplete := fun _ S f mask => incomplete_support_unchanged _ (setWeights_ne_zero hd S) f mask
    all_ranks := fun _ _ _ e S f => flatten_rank e _ (setWeights_ne_zero hd S) f
    factorization := fun _ S D => gaugedDecomposition_value _ D
    factorization_pullback := fun _ S D f h => exact_factorization_backward _ (setWeights_ne_zero hd S) D f h
    factor_lines := fun _ S f g c => gauge_projective_iff _ (setWeights_ne_zero hd S) f g c
    phase_substitutions := fun t => ⟨diagonal_substitution _ t, reflection_substitution _ t hd⟩
    traces := fun p reverse inverse u v hu hv => trace_normal_form hd hu hv p reverse inverse
    one_term := fun _ _ _ inverse ht h => one_term_nonzero ht inverse h
    protected_minor := fun t c0 c1 k0 k1 a0 a1 b0 b1 r0 r1 s0 s1 M =>
      protected_minor_monomial (deltaUnit P) t c0 c1 k0 k1 a0 a1 b0 b1 r0 r1 s0 s1 M
    reversal := source_reversal P hP
    ratios := fun M hn h => safe_ordered_ratios _ hdC hrC M hn h
    inverse_coset := ratioCoset_inverse P.positive _ hdC hrC
    disjoint_coset := fun r hr => ratioCoset_disjoint _ hdC hnotC r hr
    four_samples := fun _ t0 t1 h order choice => four_samples_coherent _ t0 t1 h order choice
    trace_cover := fun _ _ _ routing orientation h initial K0 K1 rest choice =>
      trace_cover_products_coherent routing orientation _ h initial K0 K1 rest choice
    six_to_four := fun h order p t => six_to_four_coherent _ h order p t
    polarization_fixed_parent := fun _ parity w i k hik lam a b xi =>
      Polarization.physicalGrid_fixed_parent _ parity w i k hik lam a b xi
    polarization_standard := fun _ parity w i k lam a b xi =>
      Polarization.physicalGrid_standard _ parity w i k lam a b xi
    polarization_nonzero := fun _ parity i k xi => mul_ne_zero (bitWeight_ne_zero hdC xi)
      (Polarization.constant_ne_zero _ hdC parity i k)
    polarization_ranks := fun _ parity w i k => Polarization.full_grid_ranks_iff _ hdC hrC parity w i k
    full_grid := fun _ parity i k lam h => Polarization.complete_grid_surjective _ hdC hrC parity i k lam h }

end Holant.Marked.WeightedGauge
