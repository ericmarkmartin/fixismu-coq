From Stdlib Require Export Unicode.Utf8.

Ltac crushRewriter :=
  repeat
    match goal with
      | [H : _ = _  |- _] => rewrite H
      | [H : ∀ _, _ |- _] => progress rewrite H by now trivial
    end.
