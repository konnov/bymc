proctype P(int a; short b) {
    int x = a;
    if
        :: a == 1 -> x = b;
        :: a == 2 -> x = 0;
    fi;
}
