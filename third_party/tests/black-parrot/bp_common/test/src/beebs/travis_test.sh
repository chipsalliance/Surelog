#!/bin/bash

./configure --disable-maintainer-mode || exit 1
make || exit 1
make check
res=$?

echo travis_fold:start:beebs.log
cat beebs.log
echo travis_fold:end:beebs.log

echo travis_fold:start:beebs.sum
cat beebs.sum
echo travis_fold:end:beebs.sum

exit $res
