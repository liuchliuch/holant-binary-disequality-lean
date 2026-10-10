import Holant.Proofs.Closure.ClosureSixPortSupportCard

/-! Abstract image/filter transport isolates the literal Boolean table from
its computational Finset representation during kernel checking. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort

theorem selectedImage_injOn {A B C : Type*} [DecidableEq B]
    (s : Finset A) (f : A → B) (p : B → Prop) [DecidablePred p] (r : B → C)
    (lifts : ∀ u ∈ s, ∀ v ∈ s, p (f u) → p (f v) → r (f u)=r (f v) → f u=f v) :
    Set.InjOn r {x | x ∈ (s.image f).filter p} := by
  intro x hx y hy same
  have hx' : x ∈ (s.image f).filter p := hx
  have hy' : y ∈ (s.image f).filter p := hy
  obtain ⟨hsx,hpx⟩ := Finset.mem_filter.mp hx'
  obtain ⟨hsy,hpy⟩ := Finset.mem_filter.mp hy'
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hsx
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hsy
  exact lifts u hu v hv hpx hpy same

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
