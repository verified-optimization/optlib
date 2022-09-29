# Optlib

This repo contains Lean 3 libraries used in CvxLean. When mathlib is ported to Lean 4, we can move all of these theorems into CvxLean or into Mathlib.

## Porting this repo from Lean3 to Lean4

Make sure that the latest state of `optlib` that you would like to port is on the `master` branch of this repo.

Go to `https://github.com/verified-optimization/mathport-optlib/actions/workflows/build.yml`.

On the right side of the light blue box, click on `Run workflow > Run workflow`.

Click on the appearing `optlibport` workflow, and click on `Optlibport` on the next page. Wait for the process to complete (takes 10-15 min). Open the bullet point `release` to see the tag of the new release. You will see a text like:
```
Creating new GitHub release for tag [TAG] using commit ...
```
Copy the tag `[TAG]` (e.g., `port-2022-09-29-9726f59`) into your clipboard.

Go to `https://github.com/verified-optimization/optlibport/edit/master/lakefile.lean` and edit 
the line 7 to reflect the new tag in your clipboard:
```
def tag : String := "[PASTE THE TAG HERE]"
```
Click on `Commit Changes` on the bottom of the page.

On the top right of the next page you see
```
Latest commit [COMMIT] now
```
Copy the latest commit number `[COMMIT]` into your clipboard.

Open the `lakefile.lean` of CvxLean and paste the new commit number:
```
  "https://github.com/verified-optimization/optlibport.git"@"[COMMIT]"
````
Run `lake update` and `lake build`.