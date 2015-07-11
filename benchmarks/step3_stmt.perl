#!/usr/bin/env perl
use strict;
use warnings;

# Filter-out some pieces of text from Coq output
# Author: Erik Martin-Dorel, 2014

my $input = do { local $/; <> };

$input =~ s/Finished transaction in .+?\)\s*//g;
$input =~ s/Warning: Silently use the whole real line for the following.+?You may need to unfold.+?\.\s*//gs;
print $input;
