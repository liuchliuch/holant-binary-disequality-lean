import Holant.Proofs.FiniteGroups.Stabilization.FactorWorklist
import Holant.Tractable.Criteria

/-! Exact finite decompositions obtained from the supplied saved factor tree.
No new factorization is selected. This is structural tensor closure only. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSmallArity
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open scoped BigOperators

variable {K : Type*} [Field K]

structure Packed (f : AnySignature K) where
  Index : Type
  finite : Fintype Index
  arity : Index → ℕ
  factor : (i : Index) → Signature K (arity i)
  ports : (Σ i, Fin (arity i)) ≃ Fin f.1
  scale : Kˣ
  equation : letI : Fintype Index := finite
    f.2 = fun x => (scale : K) * ∏ i, factor i (fun j => x (ports ⟨i,j⟩))

attribute [instance] Packed.finite

def Packed.single (f : AnySignature K) : Packed f where
  Index := Unit
  finite := inferInstance
  arity := fun _ => f.1
  factor := fun _ => f.2
  ports := { toFun := fun a => a.2, invFun := fun j => ⟨(),j⟩,
             left_inv := by rintro ⟨⟨⟩,j⟩; rfl, right_inv := by intro j; rfl }
  scale := 1
  equation := by funext x; simp

def Packed.join {f a b : AnySignature K} (s : ProperSplit f a b)
    (A : Packed a) (B : Packed b) : Packed f where
  Index := A.Index ⊕ B.Index
  finite := inferInstance
  arity := Sum.elim A.arity B.arity
  factor := fun i => match i with | .inl j => A.factor j | .inr j => B.factor j
  ports := (Equiv.sumSigmaDistrib (fun i => Fin (Sum.elim A.arity B.arity i))).trans
    ((Equiv.sumCongr A.ports B.ports).trans s.ports)
  scale := s.scale * A.scale * B.scale
  equation := by
    funext x
    rw [s.equation, A.equation, B.equation]
    simp only [Units.val_mul, Fintype.prod_sum_type]
    let pa : K := ∏ i, A.factor i (fun j => x (s.ports (.inl (A.ports ⟨i,j⟩))))
    let pb : K := ∏ i, B.factor i (fun j => x (s.ports (.inr (B.ports ⟨i,j⟩))))
    change (s.scale : K) * ((A.scale : K) * pa * ((B.scale : K) * pb)) =
      (s.scale : K) * (A.scale : K) * (B.scale : K) * (pa * pb)
    ring

def Packed.decomposition {f : AnySignature K} (D : Packed f) : TensorDecomposition K f.1 where
  count := Fintype.card D.Index
  arity := fun i => D.arity ((Fintype.equivFin D.Index).symm i)
  factor := fun i => D.factor ((Fintype.equivFin D.Index).symm i)
  ports := (Equiv.sigmaCongrLeft (Fintype.equivFin D.Index).symm).trans D.ports
  scale := D.scale

theorem Packed.decomposition_value {f : AnySignature K} (D : Packed f) :
    D.decomposition.value = f.2 := by
  funext x
  rw [D.equation]
  change (D.scale : K) * (∏ i, D.factor ((Fintype.equivFin D.Index).symm i)
    (fun j => x (D.ports ⟨(Fintype.equivFin D.Index).symm i,j⟩))) = _
  congr 1
  exact (Fintype.equivFin D.Index).symm.prod_comp
    (fun i => D.factor i (fun j => x (D.ports ⟨i,j⟩)))

def packedTree {f : AnySignature K} : FactorTree f → Packed f
  | .leaf f _ => Packed.single f
  | .split s a b => Packed.join s (packedTree a) (packedTree b)

theorem packedTree_leaves {f : AnySignature K} (t : FactorTree f) :
    ∀ i : (packedTree t).Index,
      (⟨(packedTree t).arity i,(packedTree t).factor i⟩ : AnySignature K) ∈ t.leaves := by
  induction t with
  | leaf f hp => intro i; simp [packedTree, Packed.single, FactorTree.leaves]
  | split s a b ia ib =>
      intro i
      cases i with
      | inl j => exact Multiset.mem_add.mpr (Or.inl (ia j))
      | inr j => exact Multiset.mem_add.mpr (Or.inr (ib j))

theorem tensorClosure_of_saved_tree {f : AnySignature K} (t : FactorTree f)
    (C : (n : ℕ) → Signature K n → Prop)
    (h : ∀ g ∈ t.leaves, C g.1 g.2) : Signature.TensorClosure C f.2 := by
  refine ⟨(packedTree t).decomposition, ?_, (packedTree t).decomposition_value⟩
  intro i
  exact h _ (packedTree_leaves t ((Fintype.equivFin (packedTree t).Index).symm i))

theorem small_tree {f : AnySignature K} (t : FactorTree f)
    (h : ∀ g ∈ t.leaves, g.1 = 1 ∨ g.1 = 2) :
    Signature.TensorClosure (fun n _ => n = 1 ∨ n = 2) f.2 :=
  tensorClosure_of_saved_tree t _ h

open Holant.Tractable

/-- One supplied tree per actual family member yields the genuine small-arity
alternative after ANY shared basis action, in particular the forward source K. -/
theorem family_tractX (F : SignatureFamily AlgebraicComplex) (hfin : F.Finite)
    (trees : (f : AnySignature AlgebraicComplex) → f ∈ F → FactorTree f)
    (small : ∀ f (hf : f ∈ F), ∀ g ∈ (trees f hf).leaves, g.1 = 1 ∨ g.1 = 2)
    (B : InvertibleKernel) : TractX (familyAction B F) := by
  refine ⟨(hfin.image _).subset (fun _ h => h.1), Or.inl ?_⟩
  rintro g ⟨⟨f,hf,rfl⟩,_pos,_nonzero⟩
  exact Or.inr (Signature.TensorClosure.map_action B.matrix
    (fun _ _ h => h) (small_tree (trees f hf) (small f hf)))

/-- The native-X interpretation requires the forward K-image, not a second
inverse-coordinate convention. -/
theorem native_family_tractX (F : SignatureFamily AlgebraicComplex) (hfin : F.Finite)
    (trees : (f : AnySignature AlgebraicComplex) → f ∈ F → FactorTree f)
    (small : ∀ f (hf : f ∈ F), ∀ g ∈ (trees f hf).leaves, g.1 = 1 ∨ g.1 = 2) :
    TractX (familyAction sourceKBasis F) :=
  family_tractX F hfin trees small sourceKBasis

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSmallArity
