# ARBAC Verification

## Description

Tool to verify role reachability of ARBAC policies.

Forward and backwards slicing are performed. The reachability algorithm is provided in both recursive and iterative forms, but the recursive one can reach the maximum recursion limit and fail.

## Usage
`python main.py`

The program will analyze all the policies in the **policies** folder. Both recursive and iterative algorithms will take approximately 6 minutes to analyze all the 9 policies in the folder.