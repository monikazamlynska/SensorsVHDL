a
    WH�`�  �                   @   s�   d Z ddlZddlZddlZddlmZmZmZm	Z	m
Z
mZmZ g d�Zed�ZdZe�d�ZG dd	� d	e�Zdd
d�Zddd�Zdd� Zdd� ZG dd� d�ZG dd� d�ZG dd� d�Zeeeef ZG dd� d�ZdS )z	 PEP 610 �    N)�Any�Dict�Iterable�Optional�Type�TypeVar�Union)�	DirectUrl�DirectUrlValidationError�DirInfo�ArchiveInfo�VcsInfo�Tzdirect_url.jsonz.^\$\{[A-Za-z0-9-_]+\}(:\$\{[A-Za-z0-9-_]+\})?$c                   @   s   e Zd ZdS )r
   N)�__name__�
__module__�__qualname__� r   r   �C/tmp/pip-unpacked-wheel-aa2x9pj2/pip/_internal/models/direct_url.pyr
      s   r
   c                 C   s4   || vr|S | | }t ||�s0td�|||���|S )z3Get value from dictionary and verify expected type.z-{!r} has unexpected type for {} (expected {}))�
isinstancer
   �format��d�expected_type�key�default�valuer   r   r   �_get   s    
��r   c                 C   s(   t | |||�}|d u r$t|� d���|S )Nz must have a value)r   r
   r   r   r   r   �_get_required(   s    r   c                 C   sF   dd� | D �} | st d��t| �dkr.t d��| d d us>J �| d S )Nc                 S   s   g | ]}|d ur|�qS �Nr   )�.0�infor   r   r   �
<listcomp>2   �    z#_exactly_one_of.<locals>.<listcomp>z/missing one of archive_info, dir_info, vcs_info�   z1more than one of archive_info, dir_info, vcs_infor   )r
   �len)�infosr   r   r   �_exactly_one_of0   s    ��r&   c                  K   s   dd� | � � D �S )z Make dict excluding None values.c                 S   s   i | ]\}}|d ur||�qS r   r   )r   �k�vr   r   r   �
<dictcomp>B   r"   z _filter_none.<locals>.<dictcomp>)�items)�kwargsr   r   r   �_filter_none?   s    r,   c                   @   s.   e Zd ZdZd	dd�Zedd� �Zdd� ZdS )
r   �vcs_infoNc                 C   s"   || _ || _|| _|| _|| _d S r   ��vcs�requested_revision�	commit_id�resolved_revision�resolved_revision_type)�selfr/   r1   r0   r2   r3   r   r   r   �__init__H   s
    zVcsInfo.__init__c              	   C   sF   |d u rd S | t |td�t |td�t|td�t|td�t|td�d�S )Nr/   r1   r0   r2   r3   )r/   r1   r0   r2   r3   )r   �strr   ��clsr   r   r   r   �
_from_dictV   s    




�zVcsInfo._from_dictc                 C   s   t | j| j| j| j| jd�S )Nr.   )r,   r/   r0   r1   r2   r3   �r4   r   r   r   �_to_dictc   s    �zVcsInfo._to_dict)NNN�r   r   r   �namer5   �classmethodr9   r;   r   r   r   r   r   E   s      �

r   c                   @   s.   e Zd ZdZd	dd�Zedd� �Zdd� ZdS )
r   �archive_infoNc                 C   s
   || _ d S r   ��hash)r4   rA   r   r   r   r5   q   s    zArchiveInfo.__init__c                 C   s   |d u rd S | t |td�d�S )NrA   r@   )r   r6   r7   r   r   r   r9   w   s    zArchiveInfo._from_dictc                 C   s   t | jd�S )Nr@   )r,   rA   r:   r   r   r   r;   ~   s    zArchiveInfo._to_dict)Nr<   r   r   r   r   r   n   s    �

r   c                   @   s.   e Zd ZdZd
dd�Zedd� �Zdd� Zd	S )r   �dir_infoFc                 C   s
   || _ d S r   ��editable)r4   rD   r   r   r   r5   �   s    zDirInfo.__init__c                 C   s"   |d u rd S | t |tddd�d�S )NrD   F)r   rC   )r   �boolr7   r   r   r   r9   �   s
    �zDirInfo._from_dictc                 C   s   t | jp
d d�S )NrC   )r,   rD   r:   r   r   r   r;   �   s    zDirInfo._to_dictN)Fr<   r   r   r   r   r   �   s    �

r   c                   @   sZ   e Zd Zddd�Zdd� Zedd� �Zdd	� Zed
d� �Z	dd� Z
edd� �Zdd� ZdS )r	   Nc                 C   s   || _ || _|| _d S r   )�urlr    �subdirectory)r4   rF   r    rG   r  