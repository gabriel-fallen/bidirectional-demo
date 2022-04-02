def hello := "world"

@[reducible] def Name := Nat

inductive SType
  | tbool
  | tfun : SType -> SType -> SType
  deriving Repr

def SType.beq : SType -> SType -> Bool
  | tbool, tbool => true
  | tfun τ1 τ2, tfun σ1 σ2 => (beq τ1 σ1) && (beq τ2 σ2)
  | _, _ => false

instance : BEq SType where
  beq := SType.beq

def SType.toString : SType -> String
  | tbool => "Bool"
  | tfun τ1 τ2 => "(" ++ toString τ1 ++ " --> " ++ toString τ2 ++ ")"

instance : ToString SType where
  toString := SType.toString

inductive STerm
  | var : Name -> STerm
  | app : STerm -> STerm -> STerm
  | abs : Name -> STerm -> STerm
  | strue
  | sfalse
  | ite : STerm -> STerm -> STerm -> STerm
  | ann : STerm -> SType -> STerm
  deriving Repr

def STerm.toString : STerm -> String
  | var n => ToString.toString n
  | app t1 t2 => "(" ++ toString t1 ++ " " ++ toString t2 ++ ")"
  | abs n t => "(λ " ++ ToString.toString n ++ ". " ++ toString t ++ ")"
  | strue  => "true"
  | sfalse => "false"
  | ite c t e => "if " ++ toString c ++ " then " ++ toString t ++ " else " ++ toString e
  | ann t τ => toString t ++ " : " ++ τ.toString

instance : ToString STerm where
  toString := STerm.toString

def Ctx := List (Name × SType)
@[reducible] def Result α := Sum String α

def Option.elim (o : Option α) (err : Unit -> β) (f : α -> β) : β := match o with
  | none   => err ()
  | some v => f v

def all_right (r1 : Result Unit) (r2 : Result Unit) (r3 : Result Unit) : Result Unit :=
  match r1 with
  | Sum.inl _ => r1
  | _ => match r2 with
         | Sum.inl _ => r2
         | _ => r3

def wrong_type (t : STerm) (τ : SType) : String :=
  "Type mismatch: the term '" ++ toString t ++ "' doesn't check against '" ++ toString τ ++ "'"

def expected_function (t : STerm) (τ : SType) : String :=
  "The term '" ++ t.toString ++ "' is expected to have a function type while having type '" ++ τ.toString ++ "'"

def incompatible_types (t : STerm) (τ1 : SType) (τ2 : SType) : String :=
  "Incompatible types: the term '" ++ t.toString ++ "' is expected to have type '" ++ τ1.toString ++ "' but got '" ++ τ2.toString ++ "'"

mutual
  open Sum
  open STerm
  open SType

  partial def check (Γ : Ctx) (t : STerm) (τ : SType) : Result Unit :=
    match t with
    | abs n t1 =>
        match τ with
        | tfun τ1 τ2 => check (List.cons ⟨n, τ1⟩ Γ) t1 τ2
        | _ => inl $ wrong_type t τ
    | STerm.ite t1 t2 t3 =>
        all_right (check Γ t1 tbool) (check Γ t2 τ) (check Γ t3 τ)
    | _ => match synth Γ t with
           | inr τ1  => if τ == τ1
              then inr ()
              else inl $ incompatible_types t τ τ1
           | inl err => inl err

  partial def synth (Γ : Ctx) (t : STerm) : Result SType :=
    match t with
    | var n =>
        (Γ.lookup n).elim
          (λ () => inl $ "Unknown variable: " ++ toString n)
          (λ τ => inr τ)
    | app t1 t2 =>
        match synth Γ t1 with
        | inr (tfun τ1 τ2) => match check Γ t2 τ1 with
            | inr ()  => inr τ2
            | inl err => inl err
        | inr τ => inl $ expected_function t1 τ
        | err   => err
    | strue | sfalse => inr tbool
    | ann t1 τ => match check Γ t1 τ with
        | inr ()  => inr τ
        | inl err => inl err
    | _ => inl $ "No rules to synthesize a type for a term '" ++ t.toString ++ "'"
end

namespace examples

open STerm
open SType

instance : OfNat Name n where
  ofNat := n

-- λ f . λ g . λ b . g (f b) : (Bool → Bool) → (Bool → Bool) → Bool → Bool
def f : Name := 1
def g : Name := 2
def b : Name := 3
def body1 :=
  abs f (
    abs g (
      abs b (
        app (var g) (app (var f) (var b))
      )
    )
  )
def btob := tfun tbool tbool
def τ1 := tfun btob (tfun btob (tfun tbool tbool))
def ex1 := ann body1 τ1

#eval synth [] ex1

def τ1_wrong := tfun btob (tfun btob tbool)
def ex1_wrong := ann body1 τ1_wrong

#eval synth [] ex1_wrong


-- λ c. λ b. λ f. λ g. if c b then f else g : (Bool -> Bool) -> Bool -> ((Bool → Bool) → Bool) -> ((Bool → Bool) → Bool) -> ((Bool → Bool) → Bool)
def c : Name := 4
def ite2 := STerm.ite (app (var c) (var b)) (var f) (var g)
def body2 := abs c (abs b (abs f (abs g ite2)))
def bbtob := tfun btob tbool
def τ2 := tfun btob (tfun tbool (tfun bbtob (tfun bbtob bbtob)))
def ex2 := ann body2 τ2

#eval synth [] ex2

def τ2_wrong := tfun btob (tfun tbool (tfun bbtob (tfun btob bbtob)))
def ex2_wrong := ann body2 τ2_wrong

#eval synth [] ex2_wrong

end examples
