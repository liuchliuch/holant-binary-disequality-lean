import Holant.Complexity.FixedGadgetSubstitution.Raw
import Holant.Complexity.FixedGadgetSubstitution.WellFormed
import Holant.Support
import Holant.Kernel
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Count
import Mathlib.Tactic


noncomputable section
namespace Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Tree
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def bit (b : Bool) : ℕ := if b then 1 else 0
def tri (x y z : Bool) : Prop := bit x+bit y+bit z=1
def ternary (x : Fin 3 → Bool) : ℚ := if tri (x 0) (x 1) (x 2) then 1 else 0
def binaryX (x : Fin 2 → Bool) : ℚ := Signature.disequality (x 0) (x 1)
def pin1 (x : Fin 1 → Bool) : ℚ := if x 0 then 1 else 0
def arity : ℕ → ℕ | 0 => 3 | 1 => 2 | _ => 1
def alphabet : (i : Fin 3) → Signature ℚ (arity i.val) :=
  Fin.cases ternary (Fin.cases binaryX (fun _ => pin1))
def edge (_ : Fin 1) : Kernel ℚ := Signature.equality

abbrev Wire := Bool × Bool
def front (x y : Bool) : Bool := x || y
def chosen (x y : Bool) : Wire := (!front x y,front x y)

/-- Each new ternary has leaves x,y and wire bit a. The old port receives
b through the physical X vertex. No bit is identified with another wire. -/
def Valid : List Bool → List Wire → Prop
  | w,[] => w.length=3 ∧ w.count true=1
  | w,(a,b)::zs => ∃ x y tail,w=x::y::tail ∧ tri x y a ∧ a≠b ∧ Valid (b::tail) zs

private theorem split_count (x y a b : Bool) (tail : List Bool)
    (ht : tri x y a) (hx : a≠b) (hc : (b::tail).count true=1) :
    (x::y::tail).count true=1 := by
  cases x <;> cases y <;> cases a <;> cases b <;>
    simp [tri,bit,List.count_cons] at ht hx hc ⊢ <;> omega
private theorem split_spec (x y : Bool) (tail : List Bool) :
    (x::y::tail).count true=1 ↔
      tri x y (!front x y) ∧ (front x y::tail).count true=1 := by
  cases x <;> cases y <;> simp [tri,bit,front,List.count_cons] <;> omega
private theorem pair_unique (x y a b : Bool) (ht : tri x y a) (hx : a≠b) :
    (a,b)=chosen x y := by
  cases x <;> cases y <;> cases a <;> cases b <;>
    simp [tri,bit,chosen,front] at ht hx ⊢
private theorem chosen_ne (x y : Bool) : (chosen x y).1≠(chosen x y).2 := by
  cases x <;> cases y <;> decide

theorem selected_leaf (w : List Bool) (zs : List Wire) (h : Valid w zs) : w.count true=1 := by
  induction zs generalizing w with
  | nil => exact h.2
  | cons z zs ih =>
      rcases z with ⟨a,b⟩
      obtain ⟨x,y,tail,rfl,ht,hx,hrest⟩ := h
      exact split_count x y a b tail ht hx (ih _ hrest)

/-- The existence and uniqueness are proved, rather than supplied as
gadget assumptions. m ternaries are added to the base ternary, so a
degree m+3 row has exactly m+1=(m+3)-2 ternaries and m X vertices. -/
theorem unique_extension (m : ℕ) (w : List Bool) (hw : w.length=m+3) :
    w.count true=1 ↔ ∃! zs : List Wire,zs.length=m ∧ Valid w zs := by
  constructor
  · intro hc
    induction m generalizing w with
    | zero =>
        refine ⟨[],⟨rfl,hw,hc⟩,?_⟩
        intro zs hz
        exact List.eq_nil_of_length_eq_zero hz.1
    | succ m ih =>
        cases w with
        | nil => simp at hw
        | cons x w =>
            cases w with
            | nil => simp at hw
            | cons y tail =>
                have hs := (split_spec x y tail).mp hc
                have hlen : (front x y::tail).length=m+3 := by simp only [List.length_cons] at hw ⊢; omega
                obtain ⟨rest,hr,hur⟩ := ih _ hlen hs.2
                refine ⟨chosen x y::rest,?_,?_⟩
                · refine ⟨by simp [hr.1],x,y,tail,rfl,hs.1,chosen_ne x y,hr.2⟩
                · intro zs hz
                  cases zs with
                  | nil => simp at hz
                  | cons z zs =>
                      rcases z with ⟨a,b⟩
                      obtain ⟨u,v,t,hword,ht,hx,hr'⟩ := hz.2
                      have hu : x=u := (List.cons.inj hword).1
                      have htail : y::tail=v::t := (List.cons.inj hword).2
                      have hv : y=v := (List.cons.inj htail).1
                      have hts : tail=t := (List.cons.inj htail).2
                      subst u
                      subst v
                      subst t
                      have hp := pair_unique x y a b ht hx
                      have hlen' : zs.length=m := by simpa using hz.1
                      have hb : b=front x y := congrArg Prod.snd hp
                      have hz' := hur zs ⟨hlen',by simpa only [hb] using hr'⟩
                      exact congrArg₂ List.cons hp hz'
  · rintro ⟨zs,hzs,_⟩
    exact selected_leaf w zs hzs.2

def weight : List Bool → List Wire → ℚ
  | w,[] => if w.length=3 ∧ w.count true=1 then 1 else 0
  | w,(a,b)::zs => match w with
    | x::y::tail => (if tri x y a then 1 else 0) *
        (Signature.disequality b a) * weight (b::tail) zs
    | _ => 0

private theorem valid_cons (x y a b : Bool) (tail : List Bool) (zs : List Wire) :
    Valid (x::y::tail) ((a,b)::zs) ↔ tri x y a ∧ a≠b ∧ Valid (b::tail) zs := by
  constructor
  · rintro ⟨u,v,t,hw,ht,hx,hr⟩
    have hu := (List.cons.inj hw).1
    have hv := (List.cons.inj (List.cons.inj hw).2).1
    have htail := (List.cons.inj (List.cons.inj hw).2).2
    subst u; subst v; subst t
    exact ⟨ht,hx,hr⟩
  · rintro ⟨ht,hx,hr⟩
    exact ⟨x,y,tail,rfl,ht,hx,hr⟩

/-- The product uses the ACTUAL ternary and binary-X entries, with no
hidden factor two. Eq edges only carry their own shared assignment bit. -/
theorem weight_indicator (w : List Bool) (zs : List Wire) :
    weight w zs=if Valid w zs then 1 else 0 := by
  induction zs generalizing w with
  | nil =>
      by_cases h : w.length=3 ∧ w.count true=1 <;> simp [weight,Valid,h]
  | cons z zs ih =>
      rcases z with ⟨a,b⟩
      cases w with
      | nil => simp [weight,Valid]
      | cons x w =>
          cases w with
          | nil => simp [weight,Valid]
          | cons y tail =>
              rw [weight,ih]
              simp only [valid_cons]
              by_cases ht : tri x y a <;> by_cases hx : a≠b <;>
                by_cases hr : Valid (b::tail) zs <;>
                  simp [ht,hx,hr,Signature.disequality,ne_comm]

theorem internal_chosen_count (w : List Bool) (zs : List Wire) (h : Valid w zs) :
    (zs.map (fun z => bit z.1+bit z.2)).sum=zs.length := by
  induction zs generalizing w with
  | nil => rfl
  | cons z zs ih =>
      rcases z with ⟨a,b⟩
      obtain ⟨x,y,t,_,_,hab,hrest⟩ := h
      have hbit : bit a+bit b=1 := by cases a <;> cases b <;> simp [bit] at hab ⊢
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      rw [hbit,ih _ hrest]
      omega

private theorem tuple_of_length (zs : List Wire) (m : ℕ) (h : zs.length=m) :
    ∃ f : Fin m → Wire,List.ofFn f=zs := by
  subst m
  exact ⟨zs.get,List.ofFn_get zs⟩

/-- The finite Boolean assignment type for exactly m physical X vertices.
Each pair contains the two DISTINCT Eq-edge bits at that X connection. -/
theorem unique_packed_extension (m : ℕ) (w : List Bool) (hw : w.length=m+3) :
    w.count true=1 ↔ ∃! f : Fin m → Wire,Valid w (List.ofFn f) := by
  constructor
  · intro hc
    obtain ⟨zs,hzs,hu⟩ := (unique_extension m w hw).mp hc
    obtain ⟨f,hf⟩ := tuple_of_length zs m hzs.1
    refine ⟨f,?_,?_⟩
    · change Valid w (List.ofFn f)
      rw [hf]
      exact hzs.2
    · intro f' hf'
      apply List.ofFn_injective
      exact (hu (List.ofFn f') ⟨by simp,hf'⟩).trans hf.symm
  · rintro ⟨f,hf,_⟩
    exact selected_leaf w (List.ofFn f) hf

def localPartition (m : ℕ) (w : List Bool) : ℚ :=
  ∑ f : Fin m → Wire,weight w (List.ofFn f)

/-- A FINITE sum of actual 0/1 cell products has scalar exactly one.
No cardinality, denotation equation or extension witness is an input. -/
theorem local_partition_exact (m : ℕ) (w : List Bool) (hw : w.length=m+3) :
    localPartition m w=if w.count true=1 then 1 else 0 := by
  by_cases hc : w.count true=1
  · obtain ⟨f,hf,hu⟩ := (unique_packed_extension m w hw).mp hc
    unfold localPartition
    rw [Finset.sum_eq_single f]
    · rw [weight_indicator]
      simp [hf,hc]
    · intro f' _hne hne
      rw [weight_indicator]
      have hn : ¬Valid w (List.ofFn f') := fun h => hne (hu f' h)
      simp [hn]
    · intro hn
      exact False.elim (hn (Finset.mem_univ f))
  · unfold localPartition
    have hz (f : Fin m → Wire) : weight w (List.ofFn f)=0 := by
      rw [weight_indicator]
      have hn : ¬Valid w (List.ofFn f) := fun h => hc (selected_leaf w _ h)
      simp [hn]
    simp only [hz,Finset.sum_const_zero,if_neg hc]

theorem pin1_exact (w : Fin 1 → Bool) :
    pin1 w=if (List.ofFn w).count true=1 then 1 else 0 := by
  cases h : w 0 <;> simp [pin1,List.ofFn_succ,h]
theorem binaryX_exact (w : Fin 2 → Bool) :
    binaryX w=if (List.ofFn w).count true=1 then 1 else 0 := by
  cases h0 : w 0 <;> cases h1 : w 1 <;>
    simp [binaryX,Signature.disequality,List.ofFn_succ,h0,h1]
theorem ternary_exact (w : Fin 3 → Bool) :
    ternary w=if (List.ofFn w).count true=1 then 1 else 0 := by
  cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;>
    simp [ternary,tri,bit,List.ofFn_succ,h0,h1,h2]

/-- Literal ordered raw tree. Internal connections are physical X vertices
between two distinct Eq edges. Boundary zero is split into the two NEW
leading boundary slots; every other original slot keeps its relative order. -/
def moved (m : ℕ) : LocalEndpoint → LocalEndpoint
  | .inl 0 => .inr (2*m,false)
  | .inl (k+1) => .inl (k+2)
  | .inr p => .inr p
def template : ℕ → Template
  | 0 => ⟨3,[(0,[.inl 0,.inl 1,.inl 2])],[]⟩
  | m+1 =>
      let old := template m
      ⟨m+4,old.vertices.map (fun row => (row.1,row.2.map (moved m))) ++
        [(1,[.inr (2*m,true),.inr (2*m+1,false)]),
         (0,[.inl 0,.inl 1,.inr (2*m+1,true)])],old.edges++[0,0]⟩
theorem template_counts (m : ℕ) :
    (template m).boundary=m+3 ∧ (template m).vertices.length=2*m+1 ∧
      (template m).edges.length=2*m := by
  induction m with
  | zero => decide
  | succ m ih => simp [template,ih.2.1,ih.2.2] <;> omega
theorem template_gate_counts (m : ℕ) :
    (template m).vertices.countP (fun row => row.1==0)=m+1 ∧
    (template m).vertices.countP (fun row => row.1==1)=m := by
  induction m with
  | zero => decide
  | succ m ih => simp [template,List.countP_map,Function.comp_def,ih.1,ih.2] <;> omega
theorem template_labels (m : ℕ) : ∀ row ∈ (template m).vertices,
    row.1<3 ∧ row.2.length=arity row.1 := by
  induction m with
  | zero => simp [template,arity]
  | succ m ih =>
      intro row hr
      simp only [template,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with ⟨old,ho,rfl⟩ | rfl | rfl
      · simpa only [List.length_map] using ih old ho
      · simp [arity]
      · simp [arity]

private theorem boundary_tail (m : ℕ) :
    ((List.range (m+3)).map Sum.inl).map (moved m) =
      .inr (2*m,false)::(List.range (m+2)).map (fun i => Sum.inl (i+2)) := by
  have hn : m+3=(m+2)+1 := by omega
  rw [hn,List.range_succ_eq_map]
  simp [List.map_map,Function.comp_def,moved]
private theorem boundary_head (n : ℕ) :
    (List.range (n+2)).map (Sum.inl : ℕ → LocalEndpoint) =
      [.inl 0,.inl 1] ++ (List.range n).map (fun i => .inl (i+2)) := by
  simp [List.range_succ_eq_map,List.map_map,Function.comp_def,Nat.add_assoc]
private theorem internal_tail (m : ℕ) :
    (edgeEnds 0 (2*m+2)).map Sum.inr =
      (edgeEnds 0 (2*m)).map Sum.inr ++
        ([.inr (2*m,false),.inr (2*m,true),
          .inr (2*m+1,false),.inr (2*m+1,true)] : List LocalEndpoint) := by
  rw [edgeEnds_add]
  simp [edgeEnds,List.map_append,List.range_succ]
private theorem endpoints_succ (m : ℕ) :
    (template (m+1)).endpoints = (template m).endpoints.map (moved m) ++
      [.inr (2*m,true),.inr (2*m+1,false),.inl 0,.inl 1,.inr (2*m+1,true)] := by
  simp [template,Template.endpoints,List.map_flatten,List.map_map,Function.comp_def]

/-- The literal compiler's multiplicities, not just its support, pass
the existing template validator. All four ends of the two NEW Eq edges
are present once; no internal X connection is a free nonphysical edge. -/
theorem template_endpoints (m : ℕ) :
    (template m).endpoints.Perm (template m).expectedEndpoints := by
  induction m with
  | zero => simp [template,Template.endpoints,Template.expectedEndpoints,edgeEnds,List.range_succ]
  | succ m ih =>
      let bs : List LocalEndpoint := (List.range (m+2)).map (fun i => .inl (i+2))
      let es : List LocalEndpoint := (edgeEnds 0 (2*m)).map Sum.inr
      have old : (template m).expectedEndpoints.map (moved m) =
          .inr (2*m,false)::(bs++es) := by
        rw [Template.expectedEndpoints,(template_counts m).1,(template_counts m).2.2]
        simp only [List.map_append]
        rw [boundary_tail]
        simp [bs,es,List.map_map,Function.comp_def,moved]
      have target : (template (m+1)).expectedEndpoints =
          [.inl 0,.inl 1] ++ bs ++ es ++
            [.inr (2*m,false),.inr (2*m,true),
             .inr (2*m+1,false),.inr (2*m+1,true)] := by
        rw [Template.expectedEndpoints,(template_counts (m+1)).1,
          (template_counts (m+1)).2.2]
        have hn : m+1+3=(m+2)+2 := by omega
        have he : 2*(m+1)=2*m+2 := by omega
        rw [hn,he,boundary_head,internal_tail]
        simp [bs,es,List.append_assoc]
      rw [endpoints_succ,target]
      have hp := (ih.map (moved m)).append_right
        [.inr (2*m,true),.inr (2*m+1,false),.inl 0,.inl 1,.inr (2*m+1,true)]
      rw [old] at hp
      apply hp.trans
      classical
      letI : BEq LocalEndpoint := ⟨fun a b => decide (a=b)⟩
      letI : LawfulBEq LocalEndpoint := {
        eq_of_beq := by
          intro a b h
          change decide (a=b)=true at h
          exact of_decide_eq_true h
        rfl := by
          intro a
          change decide (a=a)=true
          simp }
      apply List.perm_iff_count.mpr
      intro p
      simp only [List.count_append,List.count_cons,List.count_nil]
      omega

theorem template_wellFormed (m : ℕ) : (template m).WellFormed 3 1 arity := by
  refine ⟨template_labels m,?_,template_endpoints m⟩
  have hedge : ∀ k,∀ label ∈ (template k).edges,label<1 := by
    intro k
    induction k with
    | zero => simp [template]
    | succ k ih =>
        intro label hl
        simp only [template,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with old | rfl | rfl
        · exact ih label old
        · decide
        · decide
  exact hedge m

/- The next consumer obligation is the actual Template.network denotation
link, then the uniform global degree/offset emitter. Neither is silently
added as an input or asserted here. -/
end Holant.LocalDrafts.CountingHardness.UnitPerfectMatchingHolant.Tree
