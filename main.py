# ARBAC Verification - Security II Challenge
# Gobbo Jonathan 870506

import os
import time


def ur(user_assignments, user):
    return {r for (u, r) in user_assignments if u == user}


def apply_can_assign(user_assignments, rule, user_target):
    ur_target = ur(user_assignments, user_target)
    if rule[0] in {role for (user, role) in user_assignments} and rule[1].issubset(ur_target) and len(
            rule[2].intersection(ur_target)) == 0 and rule[3] not in ur_target:
        return user_assignments.union({(user_target, rule[3])})
    else:
        return user_assignments


def apply_can_revoke(user_assignments, rule, user_target):
    ur_target = ur(user_assignments, user_target)
    if rule[0] in {role for (user, role) in user_assignments} and rule[1] in ur_target:
        return {assignment for assignment in user_assignments if assignment != (user_target, rule[1])}
    else:
        return user_assignments


def verify_reachability_rec(policy, visited):
    roles, users, user_assignments, can_revoke, can_assign, goal = policy
    if frozenset(user_assignments) in visited:
        return visited, False
    if goal in {role for (user, role) in user_assignments}:
        return visited, True
    visited.add(frozenset(user_assignments))
    for rule in can_assign:
        for user in {user for (user, role) in user_assignments if role == rule[0]}:
            for user_target in users:
                user_assignments_new = apply_can_assign(user_assignments, rule, user_target)
                if not user_assignments == user_assignments_new:
                    visited_new, result = verify_reachability_rec(
                        (roles, users, user_assignments_new, can_revoke, can_assign, goal), visited)
                    if result:
                        return visited, True
                    visited = visited_new
    for rule in can_revoke:
        for user in {user for (user, role) in user_assignments if role == rule[0]}:
            for user_target in users:
                user_assignments_new = apply_can_revoke(user_assignments, rule, user_target)
                if not user_assignments == user_assignments_new:
                    visited_new, result = verify_reachability_rec(
                        (roles, users, user_assignments_new, can_revoke, can_assign, goal), visited)
                    if result:
                        return visited, True
                    visited = visited_new
    return visited, False


def verify_reachability(policy):
    return verify_reachability_rec(policy, set())


def backwards_slice(policy):
    roles, users, user_assignments, can_revoke, can_assign, goal = policy
    s_0 = {goal}
    s_i = set()
    for rule in can_assign:
        if rule[3] in s_0:
            s_i = s_i.union(rule[1].union(rule[2]).union({rule[0]}))
    s_i = s_i.union(s_0)
    while True:
        s_i_new = set()
        for rule in can_assign:
            if rule[3] in s_i:
                s_i_new = s_i_new.union(rule[1].union(rule[2]).union({rule[0]}))
        s_i_new = s_i_new.union(s_i)
        if s_i == s_i_new:  # Fixpoint S* found
            break
        else:
            s_i = s_i_new
    rs = roles.difference(s_i)  # R / S*
    # Remove from CA all the rules that assign a role in R \ S∗
    can_assign_new = {rule for rule in can_assign if rule[3] not in rs}
    # Remove from CR all the rules that revoke a role in R \ S∗
    can_revoke_new = {rule for rule in can_revoke if rule[1] not in rs}
    # Delete the roles R \ S∗
    roles_new = {role for role in roles if role not in rs}
    return roles_new, users, user_assignments, can_revoke_new, can_assign_new, goal


def forward_slice(policy):
    roles, users, user_assignments, can_revoke, can_assign, goal = policy
    s_0 = {t[1] for t in user_assignments}
    s_i = s_0.union({rule[3] for rule in can_assign if rule[1].union([rule[0]]).issubset(s_0)})
    while True:
        s_i_new = s_i.union({rule[3] for rule in can_assign if rule[1].union([rule[0]]).issubset(s_i)})
        if s_i == s_i_new:  # Fixpoint S* found
            break
        else:
            s_i = s_i_new
    rs = roles.difference(s_i)  # R / S*
    # Remove from CA all the rules that include any role in R \ S∗ in the positive preconditions or in the target
    can_assign_new = {rule for rule in can_assign if not any(r in rs for r in rule[1]) and not rule[3] in rs}
    # Remove from CR all the rules that mention any role in R \ S*
    can_revoke_new = {rule for rule in can_revoke if rule[0] not in rs and rule[1] not in rs}
    # Remove the roles R \ S∗ from the negative preconditions of all rules
    can_assign_new = {(rule[0], rule[1], rule[2].difference(rs), rule[3]) for rule in can_assign_new}
    # delete the roles R \ S∗
    roles_new = {role for role in roles if role not in rs}
    return roles_new, users, user_assignments, can_revoke_new, can_assign_new, goal


def read(filepath):
    f = open(filepath, 'r')

    # Reads roles
    roles = set(f.readline().split(' ')[1:-1])
    f.readline()

    # Reads users
    users = set(f.readline().split(' ')[1:-1])
    f.readline()

    # Reads user assignments
    ua = f.readline().split(' ')[1:-1]
    user_assignments = set([tuple(assignment.strip('<>').split(',')) for assignment in ua])
    f.readline()

    # Reads can revoke rules
    cr = f.readline().split(' ')[1:-1]
    can_revoke = set([tuple(rule.strip('<>').split(',')) for rule in cr])
    f.readline()

    # Reads can assign rules
    ca = f.readline().split(' ')[1:-1]
    can_assign = [(t[0],
                   frozenset([] if t[1] == 'TRUE' else [a for a in t[1].split('&') if not a.startswith('-')]),
                   frozenset([] if t[1] == 'TRUE' else [a.strip('-') for a in t[1].split('&') if a.startswith('-')]),
                   t[2])
                  for t in [tuple(rule.strip('<>').split(',')) for rule in ca]]
    f.readline()

    # Reads goal
    goal = f.readline().split(' ')[1]

    f.close()
    return roles, users, user_assignments, can_revoke, can_assign, goal


def main():
    start_time = time.time()
    policies = os.listdir("policies")
    for policy in policies:
        policy_data = read('policies/' + policy)
        policy_data = forward_slice(policy_data)
        policy_data = backwards_slice(policy_data)
        while True:
            policy_data_new = forward_slice(policy_data)
            policy_data_new = backwards_slice(policy_data_new)
            if policy_data_new == policy_data:
                break
            else:
                policy_data = policy_data_new
        try:
            _, result = verify_reachability(policy_data)
            print("[!] " + policy + ": " + str(result))
        except RecursionError as re:
            print("[!] " + policy + ": " + 'Probably False, recursion limit hit')

    print("--- %s seconds ---" % (time.time() - start_time))


# 10110110


if __name__ == '__main__':
    main()
