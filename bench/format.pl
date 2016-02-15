#!/usr/bin/perl

sub f {
    my ($x) = @_;
    return ($x-2147483646)
}

while (<>) {
    /IntBindingState/
    s/(\d{5}\d+)/f($1)x/eg;
    print;
}
