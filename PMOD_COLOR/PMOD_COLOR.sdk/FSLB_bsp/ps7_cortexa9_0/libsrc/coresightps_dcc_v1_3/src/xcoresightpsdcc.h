a
    WH?`?5  ?                   @   s  d Z ddlZddlZddlZddlZddlZddlmZmZm	Z	m
Z
mZmZmZ ddlmZmZ ddlmZ ddlmZ ddlmZmZ ejZede?Zer?d	nd
ZdZedddddd?Zejejej ej!ej"fZ#ejejej fZ$e?%e&?Z'dd? Z(dd? Z)dd? Z*G dd? d?Z+dS )a  Configuration management setup

Some terminology:
- name
  As written in config files.
- value
  Value associated with a name
- key
  Name combined with it's section (section.name)
- variant
  A single word describing where the configuration key-value pair came from
?    N)?Any?Dict?Iterable?List?NewType?Optional?Tuple)?ConfigurationError?!ConfigurationFileCouldNotBeLoaded)?appdirs)?WINDOWS)?
ensure_dir?enum?Kindzpip.inizpip.conf)?version?help?user?global?site?envzenv-var)?USER?GLOBAL?SITE?ENV?ENV_VARc                 C   s*   | ? ? ?dd?} | ?d?r&| dd? } | S )zFMake a name consistent regardless of source (environment or file)
    ?_?-z--?   N)?lower?replace?
startswith)?name? r"   ??/tmp/pip-unpacked-wheel-aa2x9pj2/pip/_internal/configuration.py?_normalize_name2   s    
r$   c                 C   s&   d| vrd? | ?}t|??| ?dd?S )N?.zbKey does not contain dot separated section and key. Perhaps you wanted to use 'global.{}' instead??   )?formatr	   ?split)r!   ?error_messager"   r"   r#   ?_disassemble_key<   s    ??r*   c                  C   st   dd? t ?d?D ?} tj?tjt?}tj?tj?d?t	r<dndt?}tj?t ?
d?t?}tj| tj|gtj||giS )Nc                 S   s   g | ]}t j?|t??qS r"   )?os?path?join?CONFIG_BASENAME)?.0r,   r"   r"   r#   ?
<listcomp>I   s   ?z+get_configuration_files.<locals>.<listcomp>?pip?~z.pip)r   ?site_config_dirsr+   r,   r-   ?sys?prefixr.   ?
expanduserr   ?user_config_dir?kindsr   r   r   )?global_config_files?site_config_file?legacy_config_file?new_config_filer"   r"   r#   ?get_configuration_filesG   s     ?

?
?
?r=   c                       s?   e Zd ZdZd-? fdd?	Zdd? Zdd? Zd	d
? Zdd? Zdd? Z	dd? Z
dd? Zdd? Zedd? ?Zdd? Zdd? Zdd? Zdd? Zdd ? Zd!d"? Zd#d$? Zd%d&? Zd'd(? Zd)d*? Zd+d,? Z?  ZS ).?Configurationa?  Handles management of configuration.

    Provides an interface to accessing and managing configuration files.

    This class converts provides an API that takes "section.key-name" style
    keys and stores the value associated with it as "key-name" under the
    section "section".

    This allows for a clean interface wherein the both the section and the
    key-name are preserved in an easy to manage form in the configuration files
    and the data stored is also nice.
    Nc                    sj   t ? ??  |d ur4|tvr4td?d?ttt?????|| _|| _	dd? t
D ?| _dd? t
D ?| _g | _d S )Nz5Got invalid value for load_only - should be one of