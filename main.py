# ARBAC Verification - Security II Challenge
# Gobbo Jonathan 870506

import itertools
import os
import time


def backwards_slice(policy):
    roles, users, user_assignments, can_revoke, can_assign, goal = policy
    s_0 = {goal}
    l = [rule[1] + rule[2] + [rule[0]] for rule in can_assign if rule[3] in s_0]
    join = list(itertools.chain.from_iterable(l))
    s_i = s_0.union(set(join))
    while True:
        l = [rule[1] + rule[2] + [rule[0]] for rule in can_assign if rule[3] in s_i]
        join = list(itertools.chain.from_iterable(l))
        s_i_new = s_i.union(set(join))
        if s_i == s_i_new:  # Fixpoint S* found
            break
        else:
            s_i = s_i_new
    rs = set(roles).difference(s_i)  # R / S*
    can_assign_new = [rule for rule in can_assign if rule[3] not in rs]
    can_revoke_new = [rule for rule in can_revoke if rule[1] not in rs]
    roles_new = [role for role in roles if role not in rs]
    return roles_new, users, user_assignments, can_revoke_new, can_assign_new, goal


def forward_slice(policy):
    roles, users, user_assignments, can_revoke, can_assign, goal = policy
    s_0 = set([t[1] for t in user_assignments])
    s_i = s_0.union(set([rule[3] for rule in can_assign if set(rule[1]).union([rule[0]]).issubset(s_0)]))
    while True:
        s_i_new = s_i.union(set([rule[3] for rule in can_assign if set(rule[1]).union([rule[0]]).issubset(s_i)]))
        if s_i == s_i_new:  # Fixpoint S* found
            break
        else:
            s_i = s_i_new
    rs = set(roles).difference(s_i)  # R / S*
    # Remove from CA all the rules that include any role in R \ S∗ in the positive preconditions or in the target
    can_assign_new = [rule for rule in can_assign if not any(r in rs for r in rule[1]) and not rule[3] in rs]
    # Remove from CR all the rules that mention any role in R \ S*
    can_revoke_new = [rule for rule in can_revoke if rule[0] not in rs and rule[1] not in rs]
    # Remove the roles R \ S∗ from the negative preconditions of all rules
    can_assign_new = [(rule[0], rule[1], list(set(rule[2]).difference(rs)), rule[3]) for rule in can_assign_new]
    # delete the roles R \ S∗
    roles_new = [role for role in roles if role not in rs]
    return roles_new, users, user_assignments, can_revoke_new, can_assign_new, goal


def read(filepath):
    f = open(filepath, 'r')

    # Reads roles
    roles = f.readline().split(' ')[1:-1]
    f.readline()

    # Reads users
    users = f.readline().split(' ')[1:-1]
    f.readline()

    # Reads user assignments
    ua = f.readline().split(' ')[1:-1]
    user_assignments = [tuple(assignment.strip('<>').split(',')) for assignment in ua]
    f.readline()

    # Reads can revoke rules
    cr = f.readline().split(' ')[1:-1]
    can_revoke = [tuple(rule.strip('<>').split(',')) for rule in cr]
    f.readline()

    # Reads can assign rules
    ca = f.readline().split(' ')[1:-1]
    can_assign = [(t[0], [] if t[1] == 'TRUE' else [a for a in t[1].split('&') if not a.startswith('-')],
                   [] if t[1] == 'TRUE' else [a.strip('-') for a in t[1].split('&') if a.startswith('-')], t[2]) for t
                  in
                  [tuple(rule.strip('<>').split(',')) for rule in ca]]
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
    print("--- %s seconds ---" % (time.time() - start_time))


# def main():
#     policies = os.listdir("policies")
#     for policy in policies:
#         print("\n" + policy)
#         policy_data = read('policies/' + policy)
#         print("[!] Input Policy")
#         print(policy_data)
#         policy_data = forward_slice(policy_data)
#         print("[!] Forward sliced Policy")
#         print(policy_data)
#         policy_data = backwards_slice(policy_data)
#         print("[!] Backwards sliced Policy")
#         print(policy_data)


if __name__ == '__main__':
    main()
