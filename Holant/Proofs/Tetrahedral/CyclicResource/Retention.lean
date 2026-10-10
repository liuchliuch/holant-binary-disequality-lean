import Holant.Proofs.Tetrahedral.CyclicResource.Source
import Holant.Platonic.TetrahedralLocalization.Physical


namespace Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.MainChain.CyclicBoundary
open AlgebraicRepresentatives RingHomRealization PhysicalAttachments
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.CyclicQuaternary Holant.Pauli.ExoticKlein.Fiber
noncomputable section

/-- If the specified binary labels have actually been retained in F, the
same counted graph is an F network. This is a resource-membership condition,
not a bound assumed of an unspecified realization. -/
theorem literal_retention {ι : Type*} {q : Signature ℂ 4} {B : ι → Kernel ℂ}
    {n k : ℕ} {f : Signature ℂ n} (W : Certificate q B f k)
    (F : SignatureFamily ℂ) (hq : (⟨4,q⟩ : AnySignature ℂ) ∈ F)
    (hB : ∀ i, (⟨2,PhysicalAttachments.binary (B i)⟩ : AnySignature ℂ) ∈ F) :
    copies W.circuit.network = k ∧ W.scalar ≠ 0 ∧
      W.circuit.network.denote = W.scalar • f ∧
      Gadget.Realizes F .disequality W.circuit.network.denote := by
  refine ⟨W.count,W.scalar_ne_zero,W.equation,?_⟩
  apply Gadget.realizes_network
  · intro v
    rcases W.circuit.labels v with he | ⟨i,he⟩
    · rwa [he]
    · rw [he]
      exact hB i
  · exact W.circuit.native

/-- The ACTUAL scaled network output, not only its projective representative,
has the endpoint and tensor-primality properties. -/
theorem endpoint_network {F : SignatureFamily ℂ} {N : ℕ}
    (R : Representatives F N) (q : Signature ℂ 4) (h : CountedEndpoint R q) :
    ∃ M : Network ℂ 4, copies M ≤ 2 ∧
      Gadget.Realizes (retained q R.matrix) .disequality M.denote ∧
      EvenSupported M.denote ∧ M.denote (fun _ => false) ≠ 0 ∧
      M.denote (fun _ => true) ≠ 0 ∧ ¬HasProperTensorFactor M.denote := by
  obtain ⟨g,k,hk,⟨W⟩,he,h0,h1,hp⟩ := h
  refine ⟨W.circuit.network,by rw [W.count]; exact hk,W.circuit.actual,?_,?_,?_,?_⟩
  · intro x hx
    rw [W.equation]
    change W.scalar * g x = 0
    rw [he x hx,mul_zero]
  · rw [W.equation]
    exact mul_ne_zero W.scalar_ne_zero h0
  · rw [W.equation]
    exact mul_ne_zero W.scalar_ne_zero h1
  · intro hf
    rw [W.equation] at hf
    have hi := Holant.Platonic.TetrahedralLocalization.factor_scale
      (W.scalar • g) W.scalar⁻¹ (inv_ne_zero W.scalar_ne_zero) hf
    apply hp
    simpa only [smul_smul,inv_mul_cancel₀ W.scalar_ne_zero,one_smul] using hi

/-- Expose both an actual retained parent and the exact two-child split,
then construct its finite factor tree. The children are algebraic signatures,
not assumed gadgets. No extraction reduction is hidden in this statement. -/
theorem doubled_actual_factor_tree {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (R : Representatives (mapFamily inclusion F) N) (q : Signature ℂ 4)
    (hq : Gadget.RealizesUpTo (mapFamily inclusion F) .disequality q)
    (hN : 0 < N) (d : CountedDoubled R q) :
    let d' := CountedDoubled.toOriginal R q d hq
    let b := DoubledDescent.factor hN d'
    ∃ c : AlgebraicComplex, c ≠ 0 ∧
      Gadget.Realizes F .disequality (c • DoubledDescent.square b) ∧
      Nonempty (ProperSplit (⟨4,c • DoubledDescent.square b⟩ : AnySignature AlgebraicComplex)
        ⟨2,b⟩ ⟨2,b⟩) ∧
      Nonempty (FactorTree (⟨4,c • DoubledDescent.square b⟩ : AnySignature AlgebraicComplex)) ∧
      b ≠ 0 ∧
      ¬Holant.Projective.CyclicPhasePencil.IsPhase N
        (ActualCards.walshTransfer (mapSignature inclusion b)) := by
  let d' := CountedDoubled.toOriginal R q d hq
  let b := DoubledDescent.factor hN d'
  obtain ⟨c,hc,hr,⟨s⟩⟩ := DoubledDescent.actual_parent_split hN d'
  obtain ⟨t⟩ := exists_factorTree (⟨2,b⟩ : AnySignature AlgebraicComplex)
    (DoubledDescent.factor_nonzero hN d')
  exact ⟨c,hc,hr,⟨s⟩,⟨.split s t t⟩,DoubledDescent.factor_nonzero hN d',
    DoubledDescent.factor_outside hN d'⟩

end
end Holant.LocalDrafts.TetrahedralCompletion.CyclicResource
