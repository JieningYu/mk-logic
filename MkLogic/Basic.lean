axiom Class : Type

variable {x y z w : Class}

axiom In : Class → Class → Prop
axiom Classify : (Class → Prop) → Class

instance : Membership Class Class where mem := In

@[ext] axiom Class.eq : (∀ z, z ∈ x ↔ z ∈ y) → x = y

abbrev Ensemble (x : Class) := ∃ (y : Class), x ∈ y

@[simp] axiom Class.classify {P : Class → Prop} : x ∈ Classify P ↔ (Ensemble x) ∧ (P x)

def Ensemble.intro (p : x ∈ y) : Ensemble x := Exists.intro y p

noncomputable instance : Union Class where
  union (x y : Class) := Classify fun z => z ∈ x ∨ z ∈ y
  
noncomputable instance : Inter Class where
  inter (x y : Class) := Classify fun z => z ∈ x ∧ z ∈ y
  
@[simp] theorem Union.dist : z ∈ x ∪ y ↔ (z ∈ x) ∨ (z ∈ y) := Iff.intro
  (fun h => (Class.classify.mp h).right)
  (fun h =>
    have h1 := Class.classify.mpr
    h.elim
      (fun zsx => h1 ⟨Ensemble.intro zsx, Or.inl zsx⟩)
      (fun zsy => h1 ⟨Ensemble.intro zsy, Or.inr zsy⟩)
  )

def Union.split : z ∈ x ∪ y → (z ∈ x) ∨ (z ∈ y) := Iff.mp Union.dist
def Union.intro : (z ∈ x) ∨ (z ∈ y) → z ∈ x ∪ y := Iff.mpr Union.dist

@[simp] theorem Inter.dist : z ∈ x ∩ y ↔ (z ∈ x) ∧ (z ∈ y) := Iff.intro
  (fun h => (Class.classify.mp h).right)
  (fun h => h.elim (fun zsx zsy => Class.classify.mpr ⟨Ensemble.intro zsx, ⟨zsx, zsy⟩⟩))

def Inter.split : z ∈ x ∩ y → (z ∈ x) ∧ (z ∈ y) := Iff.mp Inter.dist
def Inter.intro : (z ∈ x) ∧ (z ∈ y) → z ∈ x ∩ y := Iff.mpr Inter.dist

theorem Union.idem : y ∈ x ∪ x ↔ y ∈ x := by simp
theorem Union.idem_eq : x ∪ x = x := Class.eq fun _ => Union.idem

theorem Inter.idem : y ∈ x ∩ x ↔ y ∈ x := by simp
theorem Inter.idem_eq : x ∩ x = x := Class.eq fun _ => Inter.idem

@[symm, simp] theorem Union.comm : z ∈ x ∪ y → z ∈ y ∪ x := fun h => Union.intro (Union.split h).symm
theorem Union.comm_eq : x ∪ y = y ∪ x := Class.eq fun _ => Iff.intro Union.comm Union.comm

@[symm, simp] theorem Inter.comm : z ∈ x ∩ y → z ∈ y ∩ x := fun h => Inter.intro (Inter.split h).symm
theorem Inter.comm_eq : x ∩ y = y ∩ x := Class.eq fun _ => Iff.intro Inter.comm Inter.comm

private theorem Union.assoc_oneshot : w ∈ (x ∪ y) ∪ z → w ∈ x ∪ (y ∪ z) := fun h => Or.elim (Union.split h)
  (fun wsxy => Or.elim (Union.split wsxy) (fun wsx => Union.intro (Or.inl wsx)) (fun wsy => Union.intro (Or.inr (Union.intro (Or.inl wsy)))))
  (fun wsz => Union.intro (Or.inr (Union.intro (Or.inr wsz))))

private theorem Inter.assoc_oneshot : w ∈ (x ∩ y) ∩ z → w ∈ x ∩ (y ∩ z) := fun h =>
  have ⟨wsxy, wsz⟩ := Inter.split h; have ⟨wsx, wsy⟩ := Inter.split wsxy
  Inter.intro ⟨wsx, Inter.intro ⟨wsy, wsz⟩⟩

@[simp] theorem Union.assoc : w ∈ (x ∪ y) ∪ z ↔ w ∈ x ∪ (y ∪ z) := Iff.intro
  Union.assoc_oneshot
  fun h => Union.comm (Union.assoc_oneshot (Union.comm (Union.assoc_oneshot (Union.comm h))))
theorem Union.assoc_eq : (x ∪ y) ∪ z = x ∪ (y ∪ z) := Class.eq fun _ => Union.assoc

@[simp] theorem Inter.assoc : w ∈ (x ∩ y) ∩ z ↔ w ∈ x ∩ (y ∩ z) := Iff.intro
  Inter.assoc_oneshot
  fun h => Inter.comm (Inter.assoc_oneshot (Inter.comm (Inter.assoc_oneshot (Inter.comm h))))
theorem Inter.assoc_eq : (x ∩ y) ∩ z = x ∩ (y ∩ z) := Class.eq fun _ => Inter.assoc

@[simp] theorem Inter.dist_union : w ∈ x ∩ (y ∪ z) ↔ w ∈ (x ∩ y) ∪ (x ∩ z) := Iff.intro
  (fun h => have ⟨wsx, wsyoz⟩ := Inter.split h
    Union.intro
    ((Union.split wsyoz).elim (fun wsy => Or.inl (Inter.intro ⟨wsx, wsy⟩))
    (fun wsz => Or.inr (Inter.intro ⟨wsx, wsz⟩))))
  (fun h => Or.elim (Union.split h)
    (fun h => have ⟨wsx, wsy⟩ := Inter.split h; Inter.intro ⟨wsx, Union.intro (Or.inl wsy)⟩)
    (fun h => have ⟨wsx, wsz⟩ := Inter.split h; Inter.intro ⟨wsx, Union.intro (Or.inr wsz)⟩))
theorem Inter.dist_union_eq : x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z) := Class.eq fun _ => Inter.dist_union

def Inter.unfold_union : w ∈ x ∩ (y ∪ z) → w ∈ (x ∩ y) ∪ (x ∩ z) := Iff.mp Inter.dist_union
def Union.fold_inter : w ∈ (x ∩ y) ∪ (x ∩ z) → w ∈ x ∩ (y ∪ z) := Iff.mpr Inter.dist_union

@[simp] theorem Union.dist_inter : w ∈ x ∪ (y ∩ z) ↔ w ∈ (x ∪ y) ∩ (x ∪ z) := Iff.intro
  (fun h => Or.elim (Union.split h)
    (fun wsx => Inter.intro ⟨Union.intro (Or.inl wsx), Union.intro (Or.inl wsx)⟩)
    (fun h => have ⟨wsy, wsz⟩ := Inter.split h; Inter.intro ⟨Union.intro (Or.inr wsy), Union.intro (Or.inr wsz)⟩))
  (fun h => have ⟨h1, h2⟩ := Inter.split h
    match (Union.split h1), (Union.split h2) with
    | Or.inl wsx, _ | _, Or.inl wsx => Union.intro (Or.inl wsx)
    | Or.inr wsy, Or.inr wsz => Union.intro (Or.inr (Inter.intro ⟨wsy, wsz⟩)))
theorem Union.dist_inter_eq : x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z) := Class.eq fun _ => Union.dist_inter

def Union.unfold_inter : w ∈ x ∪ (y ∩ z) → w ∈ (x ∪ y) ∩ (x ∪ z) := Iff.mp Union.dist_inter
def Inter.fold_union : w ∈ (x ∪ y) ∩ (x ∪ z) → w ∈ x ∪ (y ∩ z):= Iff.mpr Union.dist_inter

noncomputable instance : Complement Class where
  complement x := Classify fun y => y ∉ x

@[simp] theorem Complement.compl_compl : y ∈ ~~~(~~~x) ↔ y ∈ x := Iff.intro
  (fun h =>
    have ⟨ensy, (h1 : y ∉ ~~~x)⟩ := Class.classify.mp h
    Classical.byContradiction fun fake : y ∉ x => h1 (Class.classify.mpr ⟨ensy, fake⟩))
  (fun h =>
    have h1 : y ∉ ~~~x := Classical.byContradiction fun fake : ¬¬ y ∈ ~~~x =>
      have fake : y ∈ ~~~x := Classical.not_not.mp fake
      have ⟨_, (h2 : y ∉ x)⟩ := Class.classify.mp fake
      h2 h;
    Classical.byContradiction fun fake : y ∉ ~~~(~~~x) =>
      have ensy : Ensemble y := ⟨x, h⟩
      fake (Class.classify.mpr ⟨ensy, h1⟩))
theorem Complement.compl_compl_eq : ~~~(~~~x) = x := Class.eq fun _ => Complement.compl_compl

def Complement.reduce : y ∈ ~~~(~~~x) → y ∈ x := Iff.mp Complement.compl_compl

@[simp] theorem Union.de_morgan : z ∈ ~~~(x ∪ y) ↔ z ∈ ~~~x ∩ ~~~y := Iff.intro
  (fun h =>
    have ⟨ensz, (h1 : z ∉ x ∪ y)⟩ := Class.classify.mp h
    have ⟨(znx : z ∉ x), (zny : z ∉ y)⟩ := not_or.mp (Not.imp h1 Union.intro)
    Inter.intro ⟨Class.classify.mpr ⟨ensz, znx⟩, Class.classify.mpr ⟨ensz, zny⟩⟩)
  (fun h =>
    have ⟨zcx, zcy⟩ := Inter.split h
    have ⟨ensz, znx⟩ := Class.classify.mp zcx
    have h1 := not_or.mpr ⟨znx, And.right (Class.classify.mp zcy)⟩
    have h2 : z ∉ x ∪ y := Not.intro fun fake => h1 (Union.split fake)
    Class.classify.mpr ⟨ensz, h2⟩)
theorem Union.de_morgan_eq : ~~~(x ∪ y) = ~~~x ∩ ~~~y := Class.eq fun _ => Union.de_morgan

@[simp] theorem Inter.de_morgan : z ∈ ~~~(x ∩ y) ↔ z ∈ ~~~x ∪ ~~~y := Iff.intro
  (fun h =>
    have ⟨ensz, (h1 : z ∉ x ∩ y)⟩ := Class.classify.mp h
    Union.intro (Or.imp 
      (fun h2 => Class.classify.mpr ⟨ensz, h2⟩)
      (fun h2 => Class.classify.mpr ⟨ensz, h2⟩)
      (Classical.not_and_iff_not_or_not.mp (Not.imp h1 Inter.intro))
    ))
  (fun h =>
    have h1 := Or.imp
      (fun c => Class.classify.mp c)
      (fun c => Class.classify.mp c)
      (Union.split h)
    have h2 : z ∉ x ∩ y := Classical.byContradiction fun fake =>
      have ⟨zsx, zsy⟩ := Inter.split (Classical.not_not.mp fake)
      match h1 with
      | Or.inl ⟨_, znx⟩ => znx zsx
      | Or.inr ⟨_, zny⟩ => zny zsy
    Class.classify.mpr ⟨⟨(~~~x ∪ ~~~y), h⟩, h2⟩)
theorem Inter.de_morgan_eq : ~~~(x ∩ y) = ~~~x ∪ ~~~y := Class.eq fun _ => Inter.de_morgan

noncomputable instance : Sub Class where
  sub (x y) := x ∩ ~~~y

theorem Sub.intro : z ∈ x → z ∉ y → z ∈ x - y := fun h1 h2 =>
  Inter.intro ⟨h1, Class.classify.mpr ⟨⟨x, h1⟩, h2⟩⟩

theorem Sub.split : z ∈ x - y → z ∈ x ∧ z ∉ y := fun h =>
  And.imp_right (fun h1 => And.right (Class.classify.mp h1)) (Inter.split h)

@[simp] theorem Sub.iff_and : z ∈ x - y ↔ z ∈ x ∧ z ∉ y :=
  Iff.intro Sub.split fun h => Sub.intro h.left h.right

@[simp,symm] theorem Sub.inter_assoc : w ∈ x ∩ (y - z) ↔ w ∈ (x ∩ y) - z := Inter.assoc.symm
theorem Sub.inter_assoc_eq : x ∩ (y - z) = (x ∩ y) - z := Class.eq fun _ => Sub.inter_assoc

noncomputable instance : EmptyCollection Class where
  emptyCollection := Classify fun x => x ≠ x

noncomputable abbrev Φ : Class := ∅

theorem Class.not_in_empty : x ∉ Φ := Not.intro fun fake => (Class.classify.mp fake).right rfl

@[simp] theorem Union.elim_empty : y ∈ Φ ∪ x ↔ y ∈ x := Iff.intro
  (fun h => Or.resolve_left (Union.split h) Class.not_in_empty)
  (fun h => Union.intro (Or.inr h))
theorem Union.elim_empty_eq : Φ ∪ x = x := Class.eq fun _ => Union.elim_empty

@[simp] theorem Inter.elim_empty : y ∈ Φ ∩ x ↔ y ∈ Φ := Iff.intro
  (fun h => And.left (Inter.split h))
  (fun h => (Class.not_in_empty h).elim)
theorem Inter.elim_empty_eq : Φ ∩ x = Φ := Class.eq fun _ => Inter.elim_empty

noncomputable def μ := Classify fun x => x = x

theorem Class.in_complete : x ∈ μ ↔ Ensemble x := Iff.intro
  (fun h => And.left (Class.classify.mp h))
  (fun h => Class.classify.mpr ⟨h, rfl⟩)

@[simp] theorem Union.elim_complete : y ∈ x ∪ μ ↔ y ∈ μ := Iff.intro
  (fun h => Class.in_complete.mpr ⟨x ∪ μ, h⟩)
  (fun h => Union.intro (Or.inr h))
theorem Union.elim_complete_eq : x ∪ μ = μ := Class.eq fun _ => Union.elim_complete

@[simp] theorem Inter.elim_complete : y ∈ x ∩ μ ↔ y ∈ x := Iff.intro
  (fun h => And.left (Inter.split h))
  (fun h => Inter.intro ⟨h, Class.in_complete.mpr ⟨x, h⟩⟩)
theorem Inter.elim_complete_eq : x ∩ μ = x := Class.eq fun _ => Inter.elim_complete

theorem complete_compl_empty : x ∈ μ ↔ x ∈ ~~~Φ := Iff.intro
  (fun h => Class.classify.mpr ⟨⟨μ, h⟩, Class.not_in_empty⟩)
  (fun h => Class.in_complete.mpr ⟨~~~Φ, h⟩)
theorem complete_compl_empty_eq : μ = ~~~Φ := Class.eq fun _ => complete_compl_empty

theorem empty_compl_complete : x ∈ Φ ↔ x ∈ ~~~μ := Iff.intro
  (fun h => (Class.not_in_empty h).elim)
  (fun h => have ⟨ensx, not⟩ := Class.classify.mp h; (not (Class.in_complete.mpr ensx)).elim)
theorem empty_compl_complete_eq : Φ = ~~~μ := Class.eq fun _ => empty_compl_complete

noncomputable def SInter (x : Class) := Classify fun z => ∀ y, y ∈ x → z ∈ y
noncomputable def SUnion (x : Class) := Classify fun z => ∃ y, z ∈ y ∧ y ∈ x

@[simp] theorem sinter_empty_is_complete : x ∈ SInter Φ ↔ x ∈ μ := Iff.intro
  (fun h => Class.in_complete.mpr ⟨SInter Φ, h⟩)
  (fun h => Class.classify.mpr ⟨⟨μ, h⟩, fun _ fake => (Class.not_in_empty fake).elim⟩)
theorem sinter_empty_is_complete_eq : SInter Φ = μ := Class.eq fun _ => sinter_empty_is_complete

@[simp] theorem sunion_empty_is_empty : x ∈ SUnion Φ ↔ x ∈ Φ := Iff.intro
  (fun h => have ⟨_, ⟨_, h1⟩⟩ := Class.classify.mp h; (Class.not_in_empty h1.right).elim)
  (fun h => (Class.not_in_empty h).elim)
theorem sunion_empty_is_empty_eq : SUnion Φ = Φ := Class.eq fun _ => sunion_empty_is_empty

instance : HasSubset Class where
  Subset x y := ∀ z, z ∈ x → z ∈ y

@[simp] theorem empty_is_subset : Φ ⊆ x := fun _ h => (Class.not_in_empty h).elim
@[simp] theorem complete_is_superset : x ⊆ μ := fun _ h => Class.in_complete.mpr ⟨x, h⟩
@[refl, simp] theorem subset_rfl : x ⊆ x := fun _ => id 

@[simp, symm] theorem subset_antisymm : x ⊆ y ∧ y ⊆ x ↔ x = y := Iff.intro
  (fun ⟨h1, h2⟩ => Class.eq fun z => Iff.intro (fun zsx => h1 z zsx) (fun zsy => h2 z zsy))
  (fun h => by rw[h]; simp)

@[simp] theorem subset_with_union : x ⊆ y → x ⊆ y ∪ z := fun h w wsx => Union.intro (Or.inl (h w wsx))
@[simp] theorem inter_is_subset : x ∩ y ⊆ x := fun _ h => And.left (Inter.split h)

@[simp] theorem subset_trans : x ⊆ y → y ⊆ z → x ⊆ z := fun h1 h2 w zsx => h2 w (h1 w zsx)

@[simp] theorem union_absorb_subset : x ∪ y = y ↔ x ⊆ y := Iff.intro
  (fun h => by rw[←h]; simp)
  (fun h => Class.eq fun z => Iff.intro
    (fun zsxy => (Union.split zsxy).elim (fun zsx => h z zsx) id)
    (fun zsy => Union.intro (Or.inr zsy)))
@[simp] theorem inter_absorb_subset : x ∩ y = x ↔ x ⊆ y := Iff.intro
  (fun h => by rw[←h]; rw[Inter.comm_eq]; simp)
  (fun h => Class.eq fun z => Iff.intro
    (fun zsxy => And.left (Inter.split zsxy))
    (fun zsx => Inter.intro ⟨zsx, h z zsx⟩))

theorem union_monotone : x ⊆ y → SUnion x ⊆ SUnion y := fun h _ zsux =>
  have ⟨ensz, ⟨w, ⟨zsw, wsx⟩⟩⟩ := Class.classify.mp zsux
  Class.classify.mpr ⟨ensz, ⟨w, ⟨zsw, h w wsx⟩⟩⟩
theorem inter_monotone : x ⊆ y → SInter y ⊆ SInter x := fun h _ zsiy =>
  have ⟨ensz, h1⟩ := Class.classify.mp zsiy
  Class.classify.mpr ⟨ensz, fun w wsx => have wsy := h w wsx; h1 w wsy⟩

theorem union_monotone_mem : x ∈ y → x ⊆ SUnion y := fun xsy _ zsx  =>
  Class.classify.mpr ⟨⟨x, zsx⟩, ⟨x, ⟨zsx, xsy⟩⟩⟩
theorem inter_monotone_mem : x ∈ y → SInter y ⊆ x := fun xsy _ zsiy =>
  And.right (Class.classify.mp zsiy) x xsy

noncomputable def pow (x : Class) := Classify fun y => y ⊆ x

-- axiom Class.subsets : ∀ x, Ensemble x → ∃ y, Ensemble y ∧ pow x ⊆ y
axiom Class.subsets : ∀ x, Ensemble x → ∃ y, Ensemble y ∧ (∀ z, z ⊆ x -> z ∈ y)
