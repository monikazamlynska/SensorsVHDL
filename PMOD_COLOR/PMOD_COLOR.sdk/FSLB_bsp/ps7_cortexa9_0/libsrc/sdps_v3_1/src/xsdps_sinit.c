a
    WH?`5/  ?                   @   s?  d dl Z d dlZd dlZd dlmZmZmZmZmZm	Z	m
Z
 d dlmZ d dlmZ d dlmZmZ d dlmZ d dlmZ d dlmZ d d	lmZ d d
lmZ d dlmZ d dlm Z m!Z! d dl"m#Z# d dl$m%Z%m&Z& d dl'm(Z( d dl)m*Z*m+Z+ d dl,m-Z- d dl.m/Z/ d dl0m1Z1 ddl2m3Z3m4Z4m5Z5 ddl6m7Z7 e?rXd dl8m9Z: e:e5e3e;f Z9e?<e=?Z>G dd? de%?Zdd? Z?dd? Z@dS )?    N)?TYPE_CHECKING?Dict?List?Optional?Set?Tuple?cast??canonicalize_name)?parse)?BaseReporter?ResolutionImpossible)?Resolver)?DirectedGraph)?
WheelCache)?InstallationError)?PackageFinder)?RequirementPreparer)?InstallRequirement?check_invalid_constraint_type)?RequirementSet)?BaseResolver?InstallRequirementProvider)?PipProvider)?PipDebuggingReporter?PipReporter)?
deprecated)?is_archive_file)?dist_is_editable?   )?	Candidate?
Constraint?Requirement)?Factory)?Resultc                       s6   e Zd Zh d?Zd	? fdd?	Zdd? Zdd? Z?  ZS )
r   >   zto-satisfy-onlyzonly-if-needed?eagerNc                    sJ   t ? ??  |
| jv sJ ?t||||||	|||d?	| _|| _|
| _d | _d S )N)	?finder?preparer?make_install_req?wheel_cache?use_user_site?force_reinstall?ignore_installed?ignore_requires_python?py_version_info)?super?__init__?_allowed_strategiesr#   ?factory?ignore_dependencies?upgrade_strategy?_result)?selfr'   r&   r)   r(   r*   r3   r,   r-   r+   r4   r.   ??	__class__? ?P/tmp/pip-unpacked-wheel-aa2x9pj2/pip/_internal/resolution/resolvelib/resolver.pyr0   .   s     
?zResolver.__init__c              
   C   s?  i }i }g }t |?D ]?\}}|jr?t|?}|r6t|??|?? s@q|jsNJ d??t|j?}	|	|v rr||	  |M  < q?t?|?||	< q|j	r?|jr?t|j?}
|
|vr?|||
< | j
j|dd?}|d ur|?|? qt| j
|| j| j|d?}dtjv r?t? }nt? }t||?}zd}|j||d? }| _W n@ t?yb } z&| j
?td|?|?}||?W Y d }~n
d }~0 0 t|d	?}|j?? D ?]8}|?? }|d u ?r??qx| j
?|?}|d u ?r?d
|_n?| j
j ?r?d|_n?t!|j"?|j"k?r?d|_n?|j#?s?t$|??r?d|_nr|j%?rx|j%j&?rx|j%j'?r&t(?)d|j? ?qxt*|j%j+??o>|j%j,dk}|?r^d}d}t-||ddd? d|_n?qx|j%}|?r?|j.?r?dj/|j|j"||j0?p?dd?}t(?1|? |?2|? ?qx|j3}| j
j4?5|? |S )NzConstraint must be namedr9   )Zrequested_extras)r2   ?constraintsr3   r4   ?user_requestedZPIP_RESOLVER_DEBUGi?? )Z
max_roundsz,ResolutionImpossible[Requirement, Candidate])?check_supported_wheelsFTz?%s is already installed with the same version as the provided wheel. Use --force-reinstall to force an installation of the wheel.z.zipz?Source distribution is being reinstalled despite an installed package having the same name and version as the installed package.zuse --force-reinstallz21.2i"  )?reason?replacement?gone_in?issuez?The candidate selected for download or install is a yanked version: {name!r} candidate (version {version} at {link})
Reason for being yanked: {reason}z<none given>)?name?version?linkr>   )6?	enumerate?
constraintr   r   ?match_markersrB   r
   r!   Z	from_ireqZuser_suppliedr2   Z!make_requirement_from_install_req?appendr   r3   r4   ?os?environr   r   ?
RLResolver?resolver5   r   Zget_installation_errorr   r   ?mapping?valuesZget_install_requirementZget_dist_to_uninstall?should_reinstallr+   ?parse_versionrC   ?is_editabler   Zsource_link?is_file?is_wheel?logger?infor   ?	file_path?extr   ?	is_yanked?format?yanked_reason?warning?add_named_requirement?all_requirement