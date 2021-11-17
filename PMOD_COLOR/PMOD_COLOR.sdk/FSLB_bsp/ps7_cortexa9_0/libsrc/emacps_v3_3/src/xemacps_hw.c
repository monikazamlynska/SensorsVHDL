a
    WH�`�  �                   @   s~   d dl Z d dlZd dlmZmZmZmZmZ d dlm	Z	m
Z
 d dlmZ ee	e
f Ze �e�ZG dd� d�ZG dd� d�ZdS )	�    N)�	Container�Iterator�List�Optional�Union)�LegacyVersion�Version)�stdlib_pkgsc                   @   sl   e Zd Zedd� �Zedd� �Zedd� �Zedd� �Zed	d
� �Zedd� �Z	edd� �Z
edd� �ZdS )�BaseDistributionc                 C   s
   t � �dS )a  Where the distribution is loaded from.

        A string value is not necessarily a filesystem path, since distributions
        can be loaded from other sources, e.g. arbitrary zip archives. ``None``
        means the distribution is created in-memory.
        N��NotImplementedError��self� r   �?/tmp/pip-unpacked-wheel-aa2x9pj2/pip/_internal/metadata/base.py�location   s    	zBaseDistribution.locationc                 C   s
   t � �dS )z?Value of "Metadata-Version:" in the distribution, if available.Nr   r   r   r   r   �metadata_version   s    z!BaseDistribution.metadata_versionc                 C   s
   t � �d S �Nr   r   r   r   r   �canonical_name    s    zBaseDistribution.canonical_namec                 C   s
   t � �d S r   r   r   r   r   r   �version%   s    zBaseDistribution.versionc                 C   s
   t � �d S r   r   r   r   r   r   �	installer*   s    zBaseDistribution.installerc                 C   s
   t � �d S r   r   r   r   r   r   �editable/   s    zBaseDistribution.editablec                 C   s
   t � �d S r   r   r   r   r   r   �local4   s    zBaseDistribution.localc                 C   s
   t � �d S r   r   r   r   r   r   �in_usersite9   s    zBaseDistribution.in_usersiteN)�__name__�
__module__�__qualname__�propertyr   r   r   r   r   r   r   r   r   r   r   r   r
      s    







r
   c                   @   sT   e Zd ZdZedd� �Zedd� �Zdd� Zdd	� Zd
d� Z	de
dddfdd�ZdS )�BaseEnvironmentz6An environment containing distributions to introspect.c                 C   s
   t � �d S r   r   )�clsr   r   r   �defaultB   s    zBaseEnvironment.defaultc                 C   s
   t � �d S r   r   )r   �pathsr   r   r   �
from_pathsG   s    zBaseEnvironment.from_pathsc                 C   s
   t � �dS )z=Given a requirement name, return the installed distributions.Nr   )r   �namer   r   r   �get_distributionL   s    z BaseEnvironment.get_distributionc                 C   s
   t � �dS )a  Iterate through installed distributions.

        This function should be implemented by subclass, but never called
        directly. Use the public ``iter_distribution()`` instead, which
        implements additional logic to make sure the distributions are valid.
        Nr   r   r   r   r   �_iter_distributionsQ   s    z#BaseEnvironment._iter_distributionsc                 c   sD   | � � D ]6}tjd|jtjd�}|s8t�d|j|j� q|V  qdS )z(Iterate through installed distributions.z)^([A-Z0-9]|[A-Z0-9][A-Z0-9._-]*[A-Z0-9])$)�flagsz%Ignoring invalid distribution %s (%s)N)r%   �re�matchr   �
IGNORECASE�logger�warningr   )r   �distZproject_name_validr   r   r   �iter_distributions[   s    ��z"BaseEnvironment.iter_distributionsTFc                    sb   | � � }|rdd� |D �}|s,dd� |D �}|r>dd� |D �}|rPdd� |D �}� fdd�|D �S )a  Return a list of installed distributions.

        :param local_only: If True (default), only return installations
        local to the current virtualenv, if in a virtualenv.
        :param skip: An iterable of canonicalized project names to ignore;
            defaults to ``stdlib_pkgs``.
        :param include_editables: If False, don't report editables.
        :param editables_only: If True, only report editables.
        :param user_only: If True, only report installations in the user
        site directory.
        c                 s   s   | ]}|j r|V  qd S r   )r   ��.0�dr   r   r   �	<genexpr>�   �    z?BaseEnvironment.iter_installed_distributions.<locals>.<genexpr>c                 s   s   | ]}|j s|V  qd S r   �r   r.   r   r   r   r1   �   r2   c                 s   s   | ]}|j r|V  qd S r   r3   r.   r   r   r   r1   �   r2   c                 s   s   | ]}|j r|V  qd S r   )r   r.   r   r   r   r1   �   r2   c                 3   s   | ]}|j � vr|V  qd S r   )r   r.   ��skipr   r   r1   �   r2   )r-   )r   �
local_onlyr5   �include_editables�editables_only�	user_only�itr   r4   r   �iter_installed_distributionsq   s    z,BaseEnvironment.iter_installed_distributionsN)r   r   r   �__doc__�c