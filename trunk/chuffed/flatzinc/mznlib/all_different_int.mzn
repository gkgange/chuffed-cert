% predicate all_different_int(array[int] of var int: x);
predicate all_different_int(array[int] of var int: x) =
  forall (i, j in index_set(x) where i < j) % (x[i] != x[j]);
    (int_ne(x[i], x[j]));
