a
    WH?`+?  ?                   @   s  d dl Z d dlZd dlZd dlZd dlZd dlZd dlmZmZm	Z	m
Z
mZmZmZ d dlmZmZ d dlmZ d dlmZ d dlmZ d dlmZ d dlmZ d d	lmZ d d
lmZ d dlm Z  d dl!m"Z"m#Z# d dl$m%Z% d dl&m'Z' d dl(m)Z) d dl*m+Z+ d dl,m+Z- d dl.m/Z0 d dl1m2Z2 d dl1m3Z4 d dl5m6Z6 d dl7m8Z8m9Z9 d dl:m;Z; d dl<m=Z= d dl>m?Z? d dl@mAZA d dlBmCZC d dlDmEZEmFZFmGZGmHZHmIZImJZJmKZKmLZL d dlMmNZN d dlOmPZPmQZQ d dlRmSZS d dlTmUZU e ?VeW?ZXd d!? ZYG d"d#? d#?ZZd$d%? Z[dS )&?    N)?Any?Dict?Iterable?List?Optional?Sequence?Union)?pkg_resources?six)?Marker)?Requirement)?SpecifierSet)?canonicalize_name)?Version)?parse)?Pep517HookCaller)?Distribution)?BuildEnvironment?NoOpBuildEnvironment)?InstallationError)?
get_scheme)?Link)?generate_metadata)?install_editable)?LegacyInstallFailure)?install)?install_wheel)?load_pyproject_toml?make_pyproject_path)?UninstallPathSet)?
deprecated)?direct_url_from_link)?Hashes)?
indent_log)?ask_path_exists?
backup_dir?display_path?dist_in_site_packages?dist_in_usersite?get_distribution?hide_url?redact_auth_from_url)?get_metadata)?TempDirectory?tempdir_kinds)?running_under_virtualenv)?vcsc                 C   s?   | ? tj?}tj?|?\}}t?||?}|?d?rJtj}tj?	|?d }n.|?d?sXJ ?tj
}tj?	|?d ?d?d }||||d?S )zQReturn a pkg_resources.Distribution for the provided
    metadata directory.
    z	.egg-infor   z
.dist-info?-)?project_name?metadata)?rstrip?os?sep?path?splitr	   ?PathMetadata?endswithr   ?splitext?DistInfoDistribution)?metadata_directory?dist_dir?base_dir?dist_dir_namer3   ?dist_cls?	dist_name? rC   ?A/tmp/pip-unpacked-wheel-aa2x9pj2/pip/_internal/req/req_install.py?	_get_dist<   s    
?rE   c                   @   sF  e Zd ZdZdGdd?Zdd? Zd	d
? Zdd? Zedd? ?Z	edd? ?Z
edd? ?ZdHdd?Zedd? ?ZdIdd?Zdd? Zdd? Zdd? Zd d!? Zd"d#? Zed$d%? ?Zed&d'? ?Zed(d)? ?Zed*d+? ?Zd,d-? Zed.?d/d0?Zd1d2? Zd3d4? Zed5d6? ?Zd7d8? Zd9d:? ZdJd;d<?Z d=d>? Z!dKd?d@?Z"dAdB? Z#dCdD? Z$dLdEdF?Z%dS )M?InstallRequirementz?
    Represents something that may be installed later on, may have information
    about where to fetch the relevant requirement and also contains logic for
    installing the said requirement.
    FNrC   c                 C   s?  |d u st |t?sJ |??|| _|| _|| _|| _d | _d | _| jrj|sLJ ?|jrjt	j
?t	j
?|j??| _|d u r?|r?|jr?t|j?}| | _| _d| _d | _| jr?| jjr?| jj| _|r?|| _n |r?dd? |jD ?| _nt? | _|d u r?|r?|j}|| _d | _d| _d | _d | _|?r|ng | _|	?r,|	ng | _|
?r<|
ni | _d| _|| _ || _!t"? | _#d | _$d | _%g | _&d | _'|| _(d| _)d S )NFc                 S   s   h | ]}t ?|??qS rC   )r	   ?
safe_extra??.0?extrarC   rC   rD   ?	<setcomp>?   s   z.InstallRequirement.__init__.<locals>.<setcomp>)*?
isinstancer   ?req?
comes_from?
constraint?editable?legacy_install_reason?
source_dir?is_filer5   r7   ?normpath?abspath?	file_path?urlr   ?link?original_link?original_link_is_in_wheel_cache?local_file_path?extras?set?marker?markers?satisfied_by?should_reinstall?_temp_build_dir?install_succeeded?install_options?global_options?hash_options?prepared?user_supplied?isolatedr   ?	build_envr=   ?pyproject_requires?requirements_to_check?pep517_backend?
use_pep517Zneeds_more_preparation)?selfrM   rN   rP   rX   r_   rn   ri   rd   re   rf   rO   r\   rh   rC   rC   rD   ?__init__^   s^    ?

?
zInstallRequirement.__init__c                 C   s?   | j r.t| j ?}| jrF|d?t| jj??7 }n| jrBt| jj?}nd}| jd urf|d?t| jj??7 }| j	r?t
| j	t?r?| j	}n
| j	?? }|r?|d|? d?7 }|S )Nz from {}z<InstallRequirement>z in {}z (from ?))rM   ?strrX   ?formatr+   rW   r`   r&   ?locationrN   rL   ?	from_path?ro   ?srN   rC   rC   rD   ?__str__?   s     


zInstallRequirement.__str__c                 C   s   d? | jjt| ?| j?S )Nz<{} object: {} editable={!r}>)rs   ?	__class__?__name__rr   rP   ?ro   rC   rC   rD   ?__repr__?   s    ?zInstallRequirement.__repr__c                    s>   t | ?? t? ?}? fdd?t|?D ?}dj| jjd?|?d?S )z>An un-tested helper for getting state, for debugging.
        c                 3   s   | ]}d ? |? | ?V  qdS )z{}={!r}N)rs   )rI   ?attr??
attributesrC   rD   ?	<genexpr>?   s   z2InstallRequirement.format_debug.<locals>.<genexpr>z<{name} object: {{{state}}}>z, )?name?state)?vars?sortedrs   ry   rz   ?join)ro   ?namesr?   rC   r~   rD   ?format_debug?   s    
??zInstallRequirement.format_debugc                 C   s   | j d u rd S t?| j j?S ?N)rM   r	   ?	safe_namer?   r{   rC   rC   rD   r?   ?   s    
zInstallRequirement.namec                 C   s   | j jS r?   )rM   ?	specifierr{   rC   rC   rD   r?   ?   s    zInstallRequirement.specifierc                 C   s$   | j }t|?dko"tt|??jdv S )z?Return whether I am pinned to an exact version.

        For example, some-package==1.2 is pinned; some-package>1.2 is not.
        ?   >   ?===?==)r?   ?len?next?iter?operator)ro   ?
specifiersrC   rC   rD   ?	is_pinned  s    ?zInstallRequirement.is_pinnedc                    s0   |sd}? j d ur(t? fdd?|D ??S dS d S )N)? c                 3   s   | ]}? j ?d |i?V  qdS )rJ   N)r_   ?evaluaterH   r{   rC   rD   r?     s   ?z3InstallRequirement.match_markers.<locals>.<genexpr>T)r_   ?any)ro   ?extras_requestedrC   r{   rD   ?match_markers  s    
?z InstallRequirement.match_markersc                 C   s