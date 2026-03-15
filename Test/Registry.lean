import CA

/-! # Registry attribute tests

Tests for `@[publish]` and `@[open_point]` attributes,
including the description syntax fix.
-/

-- Test 1: @[publish] without description
@[publish]
theorem test_no_desc : ∀ n m : Nat, n + m = m + n := Nat.add_comm

-- Test 2: @[publish "..."] with description
@[publish "addition is associative"]
theorem test_with_desc : ∀ a b c : Nat, a + b + c = a + (b + c) := Nat.add_assoc

-- Test 3: @[open_point] without description
@[open_point]
def test_open_no_desc : Prop := ∀ n : Nat, n * 1 = n

-- Test 4: @[open_point "..."] with description
@[open_point "Goldbach-like test"]
def test_open_with_desc : Prop := ∀ n : Nat, n + 0 = n

-- Test 5: two theorems with same mathematical content get same hash
@[publish "same fact, different name"]
theorem test_same_hash : ∀ n m : Nat, n + m = m + n := by intros; omega

-- Generate registry and verify output
#ca_registry "test_output/"
