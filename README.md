# Riam

IAM inspired policy engine written for Rust.

[![Crates.io][crates-badge]][crates-url]
[![Documentation](https://docs.rs/riam/badge.svg)](https://docs.rs/riam/)
[![Build Status][azure-badge]][azure-url]
[![MIT licensed][mit-badge]][mit-url]

[crates-badge]: https://img.shields.io/crates/v/riam?label=riam
[crates-url]: https://crates.io/crates/riam
[mit-badge]: https://img.shields.io/badge/license-MIT-blue.svg
[mit-url]: LICENSE
[azure-badge]: https://dev.azure.com/aajtodd0847/riam/_apis/build/status/aajtodd.riam?branchName=master
[azure-url]: https://dev.azure.com/aajtodd0847/riam/_build/latest?definitionId=1&branchName=master

# Overview

Riam is an access control library that provides a means of evaluating authorization decisions. In other words it answers the question of

> Is some entity allowed to carry out an action on a given resource?

You manage access to resources by creating policies and attaching them to a principal (users, group, server, etc). A policy is an object that, when associated with a principle, defines their permissions. When a principal entity (user/service/etc) attempts an action you would formulate this as an authorization request to this library to evaluate if that principal should be allowed to carry out that action. 

NOTE: this library is a rather low level primitive, unlike in AWS where policies are evaluated for you automatically when requests are made. 

In the future a higher level service will be built on top of this library to provide an authorization endpoint for evaluating decisions. Additionally an authorization proxy that can be placed in front of an HTTP API would allow for authorization decisions to be made automatically by mappting routes to permissions (e.g. from a JWT).


# Concepts

Policies in `riam` are very similar to [AWS IAM polcies](https://docs.aws.amazon.com/IAM/latest/UserGuide/access_policies.html). If you are unfamiliar with them I would look at the provided documentation link to get an idea of what they are and how they work. IAM (like) policies are an alternative to Role Based Access Control ([RBAC](https://en.wikipedia.org/wiki/Role-based_access_control)) or Access Control Lists ([ACL[(https://en.wikipedia.org/wiki/Access-control_list)). 

Notable differences from AWS IAM policies:
    - riam policies only offer "identity" based policies in AWS terms. In riam's case an identity is abstract though and can represent whatever you want (user, group, machine/service, etc)
    - `Actions` and `Resources` are also abstract and not predefined. You model your own actions and resources that fit your domain. See the guidelines on [naming](#guidelines)

**Important:** riam is not an identity provider. It doesn't do authentication and knows nothing about authenticated users. In terms of users (principals) it only stores which policies are attached to a particular principal. It's sole purpose is to evaluate authorization decisions *after authentication has already taken place*.

Policies are JSON documents that grant or deny access to carry out actions on one or more resources.

```json
{
    "name": "Blog policy",
    "statements": [
        {
            "sid": "Grant access to specific post",
            "effect": "allow",
            "actions": ["blog:edit", "blog:delete"],
            "resources": ["resource:blog:123"]
        },
        {
            "sid": "Grant access to view all blogs",
            "effect": "allow",
            "actions": "blog:view",
            "resources": "resource:blog:*"
        }
    ]
}
```

This policy allows "edit" and "delete" actions on a specific resource ("resource:blog:123") and allows "view" action on all blog resources ("resource:blog:*") via the use of a [wildcard](#wildcards).

A JSON policy document includes these elements:

* **name**: (Optional) The name given to your policy
* **statements**: One or more statements (permissions)

A statement describes a single permission (a group of one or more actions allowed or denied on one or more resources). 

* **sid**: (Optional) Include an optional statement ID to differentiate between your statements
* **effect**: Use `allow` or `deny` to indicate whether the policy allows or denies access.
* **actions**: Include a list of actions that the policy allows or denies. This may be a single scalar string `view` or a list of actions `["view", "edit"]`
* **resources**: A list of resources to which the actions apply. Like actions this can be scalar string or a list of strings.


## Multiple Statements and Multiple Policies

If you want to define more than one permission for a principal, you can use multiple statements in a single policy. You can also attach multiple policies. If you try to define multiple permissions in a single statement, your policy might not grant the access that you expect. As a best practice, break up policies by resource type(s).

It's a good idea to create functional groupings of permissions in policies. For example, maybe you have a forum website, you might create one policy for user management, one for managing posts, and another for moderator access. Regardless of the combination of multiple statements and multiple policies, riam [evaluates](#policy-evaluation) your policies the same way. 


## Policy Evaluation

riam decides if a (authorization) request is allowed or denied (for a specific principal) using the following logic:

* By default, all requests are implicitly denied. 
* An explicit allow overrides the default deny.
* An explicit deny in **any** policy overrides any allow(s).

If a policy includes multiple statements, riam applies a logical `OR` across the statements when evaluating them. If multiple policies apply to a request, riam applies a logical `OR` across all of those policies when evaluating them. 


## Wildcards

A wildcard character `*` is allowed in any policy statement action or resource. Wildcards are greedy and will match any character up to the next character in the pattern. If a pattern ends with a wildcard then the result will be a match (assuming the prefix was already a match). 

Actions and Resources are matched character for character for equality and _are_ case sensitive. 

Examples

| Pattern      | Input           | Matches |  
|--------------|-----------------|---------| 
| abc*xyz      | abcdefghgkxyz   | true    |
| a*           | abcdefghgkxyz   | true    |
| a*c          | abd             | false   |
| a*C          | abc             | false   |


## Conditions

TODO - placeholder for conditions


# Guidelines

- TODO  guidelines on naming principals, actions, and resources
- TODO guidelines on securing HTTP API if/when available
