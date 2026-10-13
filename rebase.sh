git checkout -b rebasing
MESSAGE=$(git log -1 --pretty=%B)
git checkout upstream/wip-20 -- lib/python-api/stubs/*.pyi
git checkout upstream/wip-20 -- lib/python-api/tests/*.py
git reset --soft HEAD~1
git commit -am"Preparing to rebase: copying changes from upstream/wip-20 to lib/python-api/tests/*.py"
git rebase upstream/wip-20
git reset --soft HEAD~1
git commit -am"${MESSAGE}"
./update-pytest.sh