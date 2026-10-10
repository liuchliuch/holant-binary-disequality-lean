import Holant.Proofs.FiniteGroups.Stabilization.FactorWorklist
import Holant.Proofs.FiniteGroups.Stabilization.MinimumCore
import Holant.Algebraic.FactorDescent


namespace Holant.LocalDrafts.FinitePGL2.Stabilization
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {L E : Type*} [Field L] [Field E]

def mapSignature (φ : L →+* E) (f : AnySignature L) : AnySignature E :=
  ⟨f.1, fun x => φ (f.2 x)⟩

def ProperSplit.map {f a b : AnySignature L} (s : ProperSplit f a b) (φ : L →+* E) :
    ProperSplit (mapSignature φ f) (mapSignature φ a) (mapSignature φ b) where
  left_pos := s.left_pos
  right_pos := s.right_pos
  ports := s.ports
  scale := Units.map φ s.scale
  equation := by
    funext x
    change φ (f.2 x) = _
    rw [s.equation]
    simp [mapSignature, map_mul]

theorem ProperSplit.descends (φ : L →+* E) (f : AnySignature L) (hf : f.2 ≠ 0)
    {a b : AnySignature E} (s : ProperSplit (mapSignature φ f) a b) :
    ∃ u v : AnySignature L, Nonempty (ProperSplit f u v) := by
  let join : (Fin a.1 → Bool) → (Fin b.1 → Bool) → (Fin f.1 → Bool) :=
    fun x y i => Sum.elim x y (s.ports.symm i)
  let table := fun x y => f.2 (join x y)
  have hword (x : Fin f.1 → Bool) :
      join (fun i => x (s.ports (.inl i))) (fun j => x (s.ports (.inr j))) = x := by
    funext i
    change Sum.elim (fun j => x (s.ports (.inl j))) (fun j => x (s.ports (.inr j)))
      (s.ports.symm i) = x i
    have hh (z : Fin a.1 ⊕ Fin b.1) :
        Sum.elim (fun j => x (s.ports (.inl j))) (fun j => x (s.ports (.inr j))) z = x (s.ports z) := by
      cases z <;> rfl
    exact (hh (s.ports.symm i)).trans (congrArg x (s.ports.apply_symm_apply i))
  have ht : table ≠ 0 := by
    intro hz
    apply hf
    funext x
    have h := congrFun (congrFun hz (fun i => x (s.ports (.inl i))))
      (fun j => x (s.ports (.inr j)))
    simpa only [table, hword, Pi.zero_apply] using h
  have he : ∀ x y, φ (table x y) = ((s.scale : E) * a.2 x) * b.2 y := by
    intro x y
    have h := congrFun s.equation (join x y)
    simpa [mapSignature, table, join, mul_assoc] using h
  obtain ⟨u, v, hu, hv, huv⟩ := Holant.Algebraic.FactorDescent.exists_exact_factorization
    φ table (fun x => (s.scale : E) * a.2 x) b.2 he ht
  refine ⟨⟨a.1,u⟩, ⟨b.1,v⟩, ⟨{
    left_pos := s.left_pos, right_pos := s.right_pos,
    ports := s.ports, scale := 1, equation := ?_ }⟩⟩
  funext x
  have h := huv (fun i => x (s.ports (.inl i))) (fun j => x (s.ports (.inr j)))
  simp only [table, hword] at h
  change f.2 x = (1:L) * ((u fun i => x (s.ports (.inl i))) * v (fun i => x (s.ports (.inr i))))
  rw [one_mul]
  exact h

theorem prime_mapSignature_iff (φ : L →+* E) (f : AnySignature L) :
    Prime (mapSignature φ f) ↔ Prime f := by
  constructor
  · rintro ⟨hn, hp⟩
    refine ⟨?_, ?_⟩
    · intro hz
      apply hn
      funext x
      simp [mapSignature, hz]
    · rintro ⟨a,b,⟨s⟩⟩
      exact hp ⟨mapSignature φ a, mapSignature φ b, ⟨s.map φ⟩⟩
  · rintro ⟨hn, hp⟩
    refine ⟨?_, ?_⟩
    · intro hz
      apply hn
      funext x
      apply φ.injective
      simpa only [mapSignature, Pi.zero_apply, map_zero] using congrFun hz x
    · rintro ⟨a,b,⟨s⟩⟩
      exact hp (s.descends φ f hn)

/-- Minimum arity is unchanged when the entire retained family is embedded
into the ambient coefficient field; ambient factorization gives no hidden
smaller prime. -/
def MinimumCore.mapField {F : SignatureFamily L} (core : MinimumCore F) (φ : L →+* E) :
    MinimumCore (mapSignature φ '' F) where
  signature := mapSignature φ core.signature
  retained := ⟨core.signature, core.retained, rfl⟩
  prime := (prime_mapSignature_iff φ core.signature).mpr core.prime
  nonbinary := core.nonbinary
  minimum := by
    rintro g ⟨a, ha, rfl⟩ hp hn
    exact core.minimum a ha ((prime_mapSignature_iff φ a).mp hp) hn

@[simp] theorem MinimumCore.mapField_arity {F : SignatureFamily L}
    (core : MinimumCore F) (φ : L →+* E) : (core.mapField φ).signature.1 = core.signature.1 := rfl

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
