import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockCompose

/-! Each constant occurrence receives one matching literal pin. This leaves
the coefficient unchanged while making both constant-address degrees even.
Only actual free-port parity is required of the supplied finite blocks. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockConstants
open Holant
open OrdinaryNegativeMixedBlockData
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {u s : ℕ} {a b : ℕ→ℕ}
variable (pins : Bool→Fin s) (arity : ∀q,b (pins q).val=1)

def pinNode (i : Fin u) (q : Bool) : Node (u:=u) (s:=s) (a:=a) (b:=b) i :=
  ⟨pins q,fun _=>.inl q⟩

def guards (i : Fin u) (ps : List (Bool ⊕ Fin (a i.val))) :
    List (Node (u:=u) (s:=s) (a:=a) (b:=b) i) :=
  ps.flatMap (fun q=>match q with | .inl q=>[pinNode pins i q] | .inr _=>[])

def complete (recipe : Recipe (u:=u) (s:=s) (a:=a) (b:=b)) :
    Recipe (u:=u) (s:=s) (a:=a) (b:=b) :=
  fun i=>recipe i++guards pins i (ports recipe i)

def constants {n : ℕ} (ps : List (Bool ⊕ Fin n)) : List (Bool ⊕ Fin n) :=
  ps.filter (fun q=>match q with | .inl _=>true | .inr _=>false)

include arity in
theorem guards_ports (i : Fin u) (ps : List (Bool ⊕ Fin (a i.val))) :
    (guards (b:=b) pins i ps).flatMap (fun node=>List.ofFn node.2)=constants ps := by
  induction ps with
  | nil => simp [guards,constants]
  | cons q ps ih =>
      cases q with
      | inl q =>
          simp only [guards,List.flatMap_cons,List.flatMap_append,List.flatMap_singleton] at ih ⊢
          rw [ih]
          simp [pinNode,List.ofFn_const,family,pairing,arity,constants]
      | inr q =>
          simp only [guards,List.flatMap_cons,List.nil_append] at ih ⊢
          rw [ih]
          simp [constants]

include arity in
theorem ports_complete (recipe : Recipe (u:=u) (s:=s) (a:=a) (b:=b)) (i : Fin u) :
    ports (complete pins recipe) i=ports recipe i++constants (ports recipe i) := by
  simp only [ports,complete,List.flatMap_append]
  rw [guards_ports pins arity]

theorem constants_count_left {n : ℕ} (ps : List (Bool ⊕ Fin n)) (q : Bool) :
    (constants ps).count (.inl q)=ps.count (.inl q) := by
  induction ps with
  | nil => simp [constants]
  | cons p ps ih => cases p <;> simp_all [constants,List.count_cons]

theorem constants_count_right {n : ℕ} (ps : List (Bool ⊕ Fin n)) (q : Fin n) :
    (constants ps).count (.inr q)=0 := by
  induction ps with
  | nil => simp [constants]
  | cons p ps ih => cases p <;> simp_all [constants,List.count_cons]

include arity in
theorem even_complete (recipe : Recipe (u:=u) (s:=s) (a:=a) (b:=b))
    (free : ∀i j,Even ((ports recipe i).count (.inr j))) :
    EvenRecipe (complete pins recipe) := by
  intro i q
  rw [ports_complete pins arity,List.count_append]
  cases q with
  | inl q => rw [constants_count_left]; exact ⟨_,rfl⟩
  | inr q => rw [constants_count_right,Nat.add_zero]; exact free i q

variable {K : Type} [CommSemiring K]
variable (H : (j : Fin s)→Signature K (b j.val))
variable (literal : ∀q,(⟨b (pins q).val,H (pins q)⟩ : AnySignature K)=
  ⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin q⟩)

include literal in
theorem pin_value (q : Bool) : H (pins q) (fun _=>q)=1 := by
  have aux {n : ℕ} (f : Signature K n)
      (h : (⟨n,f⟩ : AnySignature K)=⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin q⟩) :
      f (fun _=>q)=1 := by
    cases h
    simp [Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin]
  exact aux _ (literal q)

include literal in
theorem guards_value (i : Fin u) (ps : List (Bool ⊕ Fin (a i.val)))
    (x : Fin (a i.val)→Bool) :
    ((guards pins i ps).map (fun node=>H node.1 (fun j=>Sum.elim id x (node.2 j)))).prod=1 := by
  induction ps with
  | nil => simp [guards]
  | cons p ps ih =>
      cases p with
      | inl q =>
          simp only [guards,List.flatMap_cons,List.map_append,List.prod_append,
            List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,pinNode,Sum.elim_inl,id_eq,mul_one,family,pairing] at ih ⊢
          rw [pin_value pins H literal,ih,one_mul]
      | inr q => simpa only [guards,List.flatMap_cons,List.nil_append] using ih

include literal in
theorem coefficient_complete (recipe : Recipe (u:=u) (s:=s) (a:=a) (b:=b))
    (i : Fin u) (x : Fin (a i.val)→Bool) :
    coefficient H (complete pins recipe) i x=coefficient H recipe i x := by
  unfold coefficient Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient
  simp only [complete,List.map_append,List.prod_append]
  have hg := guards_value pins H literal i (ports recipe i) x
  simp only [family,pairing] at hg ⊢
  rw [hg,mul_one]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockConstants
end
