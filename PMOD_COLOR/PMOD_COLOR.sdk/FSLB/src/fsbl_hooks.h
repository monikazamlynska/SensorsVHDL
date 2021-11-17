a
    WH�`E
  �                   @   s>   d dl mZmZmZ d dlmZ d dlmZ G dd� d�ZdS )�    )�	FrozenSet�Optional�Set)�canonicalize_name)�CommandErrorc                   @   sN   e Zd ZdZddgZddd�Zdd� Zd	d
� Zedd� �Z	dd� Z
dd� ZdS )�FormatControlzGHelper for managing formats from which a package can be installed.
    �	no_binary�only_binaryNc                 C   s,   |d u rt � }|d u rt � }|| _|| _d S �N)�setr   r	   )�selfr   r	   � r   �G/tmp/pip-unpacked-wheel-aa2x9pj2/pip/_internal/models/format_control.py�__init__   s    zFormatControl.__init__c                    s:   t � �j�stS �j� jkr dS t� �fdd��jD ��S )NFc                 3   s"   | ]}t �|�t � |�kV  qd S r
   )�getattr)�.0�k��otherr   r   r   �	<genexpr>    s   �z'FormatControl.__eq__.<locals>.<genexpr>)�
isinstance�	__class__�NotImplemented�	__slots__�all)r   r   r   r   r   �__eq__   s    �zFormatControl.__eq__c                 C   s   d� | jj| j| j�S )Nz
{}({}, {}))�formatr   �__name__r   r	   �r   r   r   r   �__repr__%   s
    �zFormatControl.__repr__c                 C   s�   | � d�rtd��| �d�}d|v r`|��  |��  |�d� |d |�d�d �= d|vrd S q|D ]2}|dkrz|��  qdt|�}|�|� |�|� qdd S )N�-z7--no-binary / --only-binary option requires 1 argument.�,�:all:�   z:none:)�
startswithr   �split�clear�add�indexr   �discard)�value�targetr   �new�namer   r   r   �handle_mutual_excludes-   s&    
�


z$FormatControl.handle_mutual_excludesc                 C   sf   ddh}|| j v r|�d� n@|| jv r4|�d� n*d| j v rJ|�d� nd| jv r^|�d� t|�S )N�binary�sourcer"   )r	   r)   r   �	frozenset)r   �canonical_name�resultr   r   r   �get_allowed_formatsE   s    




z!FormatControl.get_allowed_formatsc                 C   s   | � d| j| j� d S )Nr"   )r.   r   r	   r   r   r   r   �disallow_binariesR   s    
�zFormatControl.disallow_binaries)NN)r   �
__module__�__qualname__�__doc__r   r   r   r   �staticmethodr.   r4   r5   r   r   r   r   r      s   


r   N)	�typingr   r   r   �pip._vendor.packaging.utilsr   �pip._internal.exceptionsr   r   r   r   r   r   �<module>   s                                                                                                                                                                                                                                                                                                                                                                                                                               